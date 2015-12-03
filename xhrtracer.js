/* Copyright 2015 Johannes Kloos, MPI-SWS.
 *
 * Based on a template under the following license:
 *
 * Copyright 2014 Samsung Information Systems America, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Author: Koushik Sen
// Author: Johannes Kloos
// do not remove the following comment
// JALANGI DO NOT INSTRUMENT
// In the following callbacks one can choose to not return anything.
// If all of the callbacks return nothing, we get a passive analysis where the
// concrete execution happens unmodified and callbacks are used to observe the execution.
// Once can choose to return suitable objects with specified fields in some callbacks
// to modify the behavior of the concrete execution.  For example, one could set the skip
// field of an object returned from putFieldPre to true to skip the actual putField operation.
// Similarly, one could set the result field of the object returned from a write callback
// to modify the value that is actually written to a variable. The result field of the object
// returned from a conditional callback can be suitably set to change the control-flow of the
// program execution.  In functionExit and scriptExit,
// one can set the isBacktrack field of the returned object to true to reexecute the body of
// the function from the beginning.  This in conjunction with the ability to change the
// control-flow of a program enables us to explore the different paths of a function in
// symbolic execution.
(function(sandbox) {
	function MyAnalysis(global) {
		var facts = [];
		var xhr_url = (sandbox.initParams["base"] || "http://localhost:8765") + "/facts";
		
		function send_facts() {
			if (fact_timer != null) {
				window.clearTimeout(fact_timer);
			}
			var xhr = new XMLHttpRequest();
			xhr.open("POST", xhr_url, true);
			xhr.send(JSON.stringify(facts));
		}
		
		function fact() {
			facts.push(arguments);
			if (facts.length > 10) {
				send_facts();
			} else if (fact_timer == null) {
				fact_timer = window.setTimeout(send_facts, 100);
			}
		}
		var objects = new WeakMap();
		var functions = new WeakMap();
		var objids = 0;
		var funids = 0;

		// HACK There seem to be two schools of thought on how to handle
		// global variables: They may be represented as entries in the global
		// object,
		// or as bindings in the global environment without any connection to
		// the
		// global object. We assume that each interpreter uses only one way to
		// handle globals, but we need to know which.
		fact("globals_are_properties", global.J$ === J$);

		// CAVE: The global object has to come first. We use the fact that the
		// global object has index 0 in the oracle.
		// The second argument is used to control the fields that get added.
		// In particular, we use it to exclude debris from the instrumentation.
		fact("globals", "global", objid(global,
				// XXX may want to add the standard DOM properties later
				["Infinity", "NaN", "undefined", "eval", "isFinite", "isNaN",
				 "parseFloat", "parseInt", "decodeURI", "decodeURIComponent",
				 "encodeURI", "encodeURIComponent",
				 "Array", "ArrayBuffer", "Boolean", "DataView", "Date", "Error",
				 "EvalError", "Float32Array", "Float64Array", "Function",
				 "Int8Array", "Int16Array", "Int32Array", "Map", "Number", "Object",
				 "Proxy", "Promise", "RangeError", "ReferenceError", "RegExp",
				 "Set", "String", "Symbol", "SyntaxError", "TypeError",
				 "Uint8Array", "Uint8ClampedArray", "Uint16Array", "Uint32Array",
				 "URIError", "WeakSet", "WeakMap", "JSON", "Math", "Reflect"]));
		fact("globals", "Object", objid(Object));
		fact("globals", "Function", objid(Function));
		fact("globals", "Boolean", objid(Boolean));
		fact("globals", "Error", objid(Error));
		fact("globals", "Number", objid(Number));
		fact("globals", "Math", objid(Math));
		fact("globals", "Date", objid(Date));
		fact("globals", "String", objid(String));
		fact("globals", "RegExp", objid(RegExp));
		fact("globals", "Array", objid(Array));
		fact("globals", "JSON", objid(JSON));

		// recurse along prototype chain
		function filter_special(name, limit) {
			if (limit) {
				if (limit.indexOf(name) == -1) return true;
			}
		    return (name == "caller" || name == "callee" || name == "arguments" || name == "*J$IID*" || name == "*J$SID*");
		}
		function describe_level(obj, desc, limit) {
			var props = Object.getOwnPropertyNames(obj);
			for (var i = 0; i < props.length; i++) {
				var prop = props[i];
				if (filter_special(prop, limit))
					continue;
				var propdesc = Object.getOwnPropertyDescriptor(obj, prop);
				if (propdesc == undefined)
					propdesc = {};
				var skip_value = false;
				if (propdesc["get"]) {
					propdesc.get = objid(propdesc.get)
					skip_value = true;
				}
				if (propdesc["set"]) {
					propdesc.set = objid(propdesc.set)
				}
				if (!skip_value)
					propdesc.value = objid(obj[prop]);
				else
					propdesc.value = undefined;
				desc[prop] = propdesc;
			}
			var proto = Object.getPrototypeOf(obj);
			if (proto !== null && proto !== Object.getPrototypeOf(obj))
				return describe_level(obj, desc);
			else
				return desc;
		}

		function describeobj(obj, limit) {
		    return describe_level(obj, {}, limit);
		}
		function funcid(obj) {
			// We know that obj is of type function
			if (functions.has(obj)) {
				return functions.get(obj);
			} else {
				var id = funids++;
				functions.set(obj, id);
				fact("function", id, {
					instrumented : obj.toString(),
					obj : objid(obj)
				});
				return id;
			}
		}

		function objid(obj, limit) {
			switch (typeof obj) {
			case "undefined":
				return {
					type : "undefined"
				};
			case "boolean":
			case "number":
			case "string":
			case "symbol":
				return {
					type : typeof obj,
					val : obj.toString()
				}
			case "function":
				if (objects.has(obj)) {
					return {
						type : "function",
						id : objects.get(obj),
						funid : funcid(obj)
					}
				} else {
					var id = objids++;
					objects.set(obj, id);
					facts("object", id, describeobj(obj, limit));
					return {
						type : "function",
						id : id,
						funid : funcid(obj)
					}
				}
			case "object":
				if (obj === null) {
					return {
						type : "null"
					}
				} else if (objects.has(obj)) {
					return {
						type : "object",
						id : objects.get(obj)
					}
				} else {
					var id = objids++;
					objects.set(obj, id);
					facts("object", id, describeobj(obj, limit));
					return {
						type : "object",
						id : id
					}
				}
			default:
				if (objects.has(obj)) {
					return {
						type : typeof obj,
						id : objects.get(obj)
					}
				} else {
					var id = objids++;
					objects.set(obj, id);
					facts("object", id, { external: true })
					return {
						type : typeof obj,
						id : id
					}
				}
			}
		}

		this.invokeFunPre = function(iid, f, base, args, isConstructor,
				isMethod) {
			fact("step", {
				step : "funpre",
				iid : iid,
				f : objid(f),
				base : objid(base),
				args : objid(args),
				isConstructor : isConstructor,
				isMethod : isMethod
			});
		};

		this.invokeFun = function(iid, f, base, args, result, isConstructor,
				isMethod) {
			fact("step", {
				step : "funpost",
				iid : iid,
				f : objid(f),
				base : objid(base),
				args : objid(args),
				isConstructor : isConstructor,
				isMethod : isMethod,
				result : objid(result)
			});
		};

		this.literal = function(iid, val, hasGetterSetter) {
			// Special handling for function literals.
			var id = objid(val);
			fact("step", {
				step : "literal",
				iid : iid,
				val : id,
				hasGetterSetter : hasGetterSetter
			});
			if (typeof val == "function") {
				var data = J$.smap[J$.sid];
				if (data[iid]) {
				    var pos = data[iid].map(function(x) {
					    return x - 1
				    });
				    var lines = data.code.split("\n");
				    var text;
				    if (pos[0] == pos[2]) {
					    text = lines[pos[0]].substr(pos[1], pos[3] - pos[1]);
				    } else {
					    text = lines[pos[0]].substr(pos[1]);
					    for (var i = pos[0] + 1; i < pos[2]; i++) {
						    text += "\n" + lines[i];
					    }
					    text += "\n" + lines[pos[2]].substr(0, pos[3]);
				    }
				    fact("function-uninstrumented", id.funid, text);
				}
			}
		};

		this.forinObject = function(iid, val) {
			fact("step", {
				step : "forin",
				iid : iid,
				val : objid(val)
			});
		};

		this.declare = function(iid, name, val, isArgument, argumentIndex,
				isCatchParam) {
			fact("step", {
				step : "declare",
				iid : iid,
				name : name,
				val : objid(val),
				isArgument : isArgument,
				argumentIndex : argumentIndex,
				isCatchParam : isCatchParam
			});
		};

		this.getFieldPre = function(iid, base, offset, isComputed, isOpAssign,
				isMethodCall) {
			fact("step", {
				step : "getpre",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				isComputed : isComputed,
				isOpAssign : isOpAssign,
				isMethodCall : isMethodCall
			});
		};

		this.getField = function(iid, base, offset, val, isComputed,
				isOpAssign, isMethodCall) {
			fact("step", {
				step : "getpost",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign,
				isMethodCall : isMethodCall
			});
		};

		this.putFieldPre = function(iid, base, offset, val, isComputed,
				isOpAssign) {
			fact("step", {
				step : "putpre",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign
			});
		};

		this.putField = function(iid, base, offset, val, isComputed, isOpAssign) {
			fact("step", {
				step : "putpost",
				iid : iid,
				base : objid(base),
				offset : offset.toString(),
				val : objid(val),
				isComputed : isComputed,
				isOpAssign : isOpAssign
			});
		};

		this.read = function(iid, name, val, isGlobal, isScriptLocal) {
			fact("step", {
				step : "read",
				iid : iid,
				name : name,
				val : objid(val),
				isGlobal : isGlobal,
				isScriptLocal : isScriptLocal
			});
		};

		this.write = function(iid, name, val, lhs, isGlobal, isScriptLocal) {
			fact("step", {
				step : "write",
				iid : iid,
				name : name,
				val : objid(val),
				lhs : objid(lhs),
				isGlobal : isGlobal,
				isScriptLocal : isScriptLocal
			});
		};

		this._return = function(iid, val) {
			fact("step", {
				step : "return",
				iid : iid,
				val : objid(val)
			});
		};

		this._throw = function(iid, val) {
			fact("step", {
				step : "throw",
				iid : iid,
				val : objid(val)
			});
		};

		this.functionEnter = function(iid, f, dis, args) {
			fact("step", {
				step : "funcenter",
				iid : iid,
				f : objid(f),
				"this" : objid(dis),
				args : objid(args)
			});
		};

		this.functionExit = function(iid, returnVal, wrappedExceptionVal) {
			fact("step", {
				step : "funcexit",
				iid : iid,
				ret : objid(returnVal),
				exc : objid(wrappedExceptionVal)
			});
		};

		this.scriptEnter = function(iid, instrumentedFileName, originalFileName) {
			fact("step", {
				step : "scriptenter"
			});
		};

		this.scriptExit = function(iid, wrappedExceptionVal) {
			if (wrappedExceptionVal === undefined) {
				fact("step", {
					step : "scriptexit"
				});
			} else {
				fact("step", {
					step : "scriptexc",
					exc : objid(wrappedExceptionVal)
				});
			}
		};

		this.binaryPre = function(iid, op, left, right, isOpAssign,
				isSwitchCaseComparison, isComputed) {
			fact("step", {
				step : "binarypre",
				iid : iid,
				op : op,
				left : objid(left),
				right : objid(right),
				isOpAssign : isOpAssign,
				isSwitchComparison : isSwitchCaseComparison,
				isComputed : isComputed
			});
		};

		this.binary = function(iid, op, left, right, result, isOpAssign,
				isSwitchCaseComparison, isComputed) {
			fact("step", {
				step : "binarypost",
				iid : iid,
				op : op,
				left : objid(left),
				right : objid(right),
				isOpAssign : isOpAssign,
				isSwitchComparison : isSwitchCaseComparison,
				isComputed : isComputed,
				result : objid(result)
			});
		};

		this.unaryPre = function(iid, op, left) {
			fact("step", {
				step : "unarypre",
				iid : iid,
				op : op,
				left : objid(left)
			});
		};

		this.unary = function(iid, op, left, result) {
			fact("step", {
				step : "unarypost",
				iid : iid,
				op : op,
				left : objid(left),
				result : objid(result)
			});
		};

		this.conditional = function(iid, result) {
			fact("step", {
				step : "conditional",
				iid : iid,
				result : objid(result)
			});
		};

		this.endExpression = function(iid) {
			fact("step", {
				step : "exprend",
				iid : iid
			});
		};

		this.endExecution = function() {
			fact("end");
		};

		this._with = function(iid, val) {
			fact("step", {
				step : "with",
				iid : iid,
				val : val
			});
		};
	}
	sandbox.analysis = new MyAnalysis(this);
})(J$);
