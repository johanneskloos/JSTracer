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
		var objects = new WeakMap();
		var functions = new WeakMap();
		var objids = 0;
		var funids = 0;
		var init = false;

		function text(string) {
			return window.document.createTextNode(string);
		}
		function getId(name) {
			return window.document.getElementById(name);
		}
		function appendChildren(node, contents) {
			if (Array.isArray(contents)) {
				for (i = 0; i < contents.length; i++) {
					node.appendChild(contents[i]);
				}
			} else {
				node.appendChild(contents);
			}
			return node;
		}
		function create_with_class(tag, clazz) {
			var elt = window.document.createElement(tag);
			if (clazz) elt.setAttribute("class", clazz);
			return elt;
		}
		function div(contents, clazz) {
			return appendChildren(create_with_class("div", clazz), contents);
		}
		function span(contents, clazz) {
			return appendChildren(create_with_class("span", clazz),	contents);
		}
		function href(link, contents) {
			var href = window.document.createElement("a");
			href.setAttribute("href", link);
			return appendChildren(href, contents);
		}
		function anchor(link, contents) {
			var anchor = window.document.createElement("a");
			anchor.setAttribute("id", link);
			return appendChildren(anchor, contents);
		}
		function add_descpair(base, label, content) {
			var desc1 = appendChildren(window.document.createElement("dt"),
					label);
			var desc2 = appendChildren(window.document.createElement("dd"),
					content);
			return appendChildren(base, [ desc1, desc2 ]);
		}
		function add_tablecells(base, header, content) {
			var row = window.document.createElement("tr");
			var cells = [appendChildren(window.document.createElement("th"), header)];
			for (var i = 0; i < content.length; i++) {
				cells.push (appendChildren(window.document.createElement("td"), content[i]))
			}
			base.appendChild(appendChildren(row, cells));
		}
		function list_item(label, contents) {
			return appendChildren(window.document.createElement("li"), anchor(
					label, contents));
		}
		function desclist(base) {
			var dl = window.document.createElement("dl");
			appendChildren(base, dl);
			return dl;
		}

		function identify_global(name, obj, fields) {
			add_descpair(getId("globals"), text(name), objid(obj, fields));
		}

		// recurse along prototype chain
		function filter_special(name, limit) {
			if (limit) {
				if (limit.indexOf(name) == -1)
					return true;
			}
			return (name == "caller" || name == "callee" || name == "arguments"
					|| name == "*J$IID*" || name == "*J$SID*");
		}
		function describe_level(obj, base, limit) {
			var props = Object.getOwnPropertyNames(obj);
			for (var i = 0; i < props.length; i++) {
				var prop = props[i];
				if (filter_special(prop, limit))
					continue;
				var propdesc = Object.getOwnPropertyDescriptor(obj, prop);
				if (propdesc == undefined) {
					continue;
				}
				var desc = [];
				if (propdesc["get"]) {
					desc.push(text("Getter: "));
					desc.push(objid(propdesc.get));
				} else {
					desc.push(objid(obj[prop]));
				}
				if (propdesc["set"]) {
					desc.push(text(", Setter: "));
					desc.push(objid(propdesc.set));
				}
				var flags = [];
				if (!propdesc["enumerable"]) {
					flags.push("not enumerable")
				}
				if (!propdesc["configurable"]) {
					flags.push("not configurable")
				}
				if (!propdesc["writable"]) {
					flags.push("not writable")
				}
				if (flags !== []) {
					desc.push(text(" ("));
					desc.push(text(Array.prototype.join.call(flags, ", ")));
					desc.push(text(")"));
				}
				add_tablecells(base, text(prop), [desc]);
			}
			var proto = Object.getPrototypeOf(obj);
			if (proto !== null && proto !== Object.getPrototypeOf(obj))
				describe_level(obj, base);
		}

		function describeobj(obj, id, limit) {
			var base = window.document.createElement("table");
			var litem = list_item("obj" + id, base);
			getId("objects").appendChild(litem);
			describe_level(obj, base, limit);
		}
		function funcid(obj, uninstrumented) {
			// We know that obj is of type function
			if (functions.has(obj)) {
				return functions.get(obj);
			} else {
				var id = funids++;
				functions.set(obj, id);
				var content = [ objid(obj) ];
				var code = uninstrumented ? text(uninstrumented) : text(obj
						.toString());
				content.push(appendChildren(window.document
						.createElement("blockquote"), code));
				getId("functions").appendChild(list_item(id, content));
				return id;
			}
		}

		function objid(obj, limit) {
			switch (typeof obj) {
			case "undefined":
				return text("undefined");
			case "boolean":
			case "number":
				return text(obj.toString());
			case "string":
				return span(text("\"" + obj + "\""), "string");
			case "symbol":
				return text("symbol:" + obj.toString());
			case "function":
				var id;
				var fun;
				if (objects.has(obj)) {
					id = objects.get(obj);
					fun = funcid(obj);
				} else {
					id = objids++;
					objects.set(obj, id);
					describeobj(obj, id, limit);
					fun = funcid(obj);
				}
				return span([ text("function "), href("#obj" + id, text(id)),
						text("/"), href("#fun" + fun, text(fun)) ], "objref");
			case "object":
				if (obj === null) {
					return text("null");
				}
				var id;
				if (objects.has(obj)) {
					id = objects.get(obj)
				} else {
					id = objids++;
					objects.set(obj, id);
					describeobj(obj, id, limit);
				}
				return span([ text("object "), href("#obj" + id, text(id)) ], "objref");
			default:
				var id;
				if (objects.has(obj)) {
					id = objects.get(obj);
				} else {
					var id = objids++;
					objects.set(obj, id);
					getId("objects").appendChild(
							text("exotic object, type: " + typeof obj));
				}
				return span([ text("Exotic object (typeof obj) "),
						href("#obj" + id, text(id)) ], "objref");
			}
		}

		function dump_event(clazz, content) {
			console.log("dump_event");
			var elt = window.document.createElement("li");
			elt.setAttribute("class", clazz)
			getId("trace").appendChild(
				appendChildren(elt, content)
			);
		}
		
		function init_globals() {
			// CAVE: The global object has to come first. We use the fact that
			// the
			// global object has index 0 in the oracle.
			// The second argument is used to control the fields that get added.
			// In particular, we use it to exclude debris from the
			// instrumentation.

			identify_global("global", global,
					[ "Infinity", "NaN", "undefined",
					"eval", "isFinite", "isNaN", "parseFloat", "parseInt",
					"decodeURI", "decodeURIComponent", "encodeURI",
					"encodeURIComponent", "Array", "ArrayBuffer", "Boolean",
					"DataView", "Date", "Error", "EvalError", "Float32Array",
					"Float64Array", "Function", "Int8Array", "Int16Array",
					"Int32Array", "Map", "Number", "Object", "Proxy",
					"Promise", "RangeError", "ReferenceError", "RegExp", "Set",
					"String", "Symbol", "SyntaxError", "TypeError",
					"Uint8Array", "Uint8ClampedArray", "Uint16Array",
					"Uint32Array", "URIError", "WeakSet", "WeakMap", "JSON",
					"Math", "Reflect" ]);

			identify_global("Object", Object);
			identify_global("Function", Function);
			identify_global("Boolean", Boolean);
			identify_global("Error", Error);
			identify_global("Number", Number);
			identify_global("Math", Math);
			identify_global("Date", Date);
			identify_global("String", String);
			identify_global("RegExp", RegExp);
			identify_global("Array", Array);
			identify_global("JSON", JSON);

		}

		function format_call_type(isConstructor, isMethod) {
			return isConstructor ?
						(isMethod ? "method-constructor??? " : "constructor ") :
						(isMethod ? "method " : "function ");
		}
		this.invokeFunPre = function(iid, f, base, args, isConstructor,
				isMethod) {
			dump_event("precall", [text("Call "),
			            text(format_call_type(isConstructor, isMethod)), text("on function "), objid(f),
			            text(" with this="), objid(base), text(" and argument array "), objid(args)]);
		};

		this.invokeFun = function(iid, f, base, args, result, isConstructor,
				isMethod) {
			dump_event("postcall", [text("Called "),
			            text(format_call_type(isConstructor, isMethod)), text("on function "), objid(f),
			            text(" with this="), objid(base), text(" and argument array "), objid(args),
			            text(" returns "), objid(result)]);
		};

		this.literal = function(iid, val, hasGetterSetter) {
			// Special handling for function literals.
			if (typeof val == "function") {
				var data = J$.smap[J$.sid];
				if (data[iid]) {
					var pos = data[iid].map(function(x) {
						return x - 1
					});
					var lines = data.code.split("\n");
					var ftext;
					if (pos[0] == pos[2]) {
						ftext = lines[pos[0]].substr(pos[1], pos[3] - pos[1]);
					} else {
						ftext = lines[pos[0]].substr(pos[1]);
						for (var i = pos[0] + 1; i < pos[2]; i++) {
							ftext += "\n" + lines[i];
						}
						ftext += "\n" + lines[pos[2]].substr(0, pos[3]);
					}
					funcid(val, ftext);
				}
			}
			dump_event ("literal", [hasGetterSetter ? text("Literal with getter and setter: ") : text("Literal: "),
					objid(val)]);
		};

		this.forinObject = function(iid, val) {
			dump_event("forin", [text("for-in on ", objid(val))]);
		};

		this.declare = function(iid, name, val, isArgument, argumentIndex,
				isCatchParam) {
			var valid = objid(val);
			if (isArgument && argumentIndex === -1) {
				dump_event("declare-argarray", [text("Binding arguments array ("), valid, text(") to " + name)]);
			} else if (isArgument && argumentIndex >= 0) {
				dump_event("declare-arg", [text("Binding formal parameter " + argumentIndex + " with value "),
				            valid, text(") to " + name)]);
			} else if (isCatchParam) {
				dump_event("declare-catch", [text("Catching exception with value "),
				            valid, text(" in " + name)]);
			} else {
				dump_event("declare-local", [text("Declaring local variable " + name + " with value "), valid]);
			}
		};

		this.getField = function(iid, base, offset, val, isComputed,
				isOpAssign, isMethodCall) {
			dump_event("read-field", [text("Reading field " + offset + " from object "), objid(base),
			            text(", yielding "), objid(val)]);
		};

		this.putField = function(iid, base, offset, val, isComputed, isOpAssign) {
			dump_event("write-field", [text("Writing field " + offset + " in object "), objid(base),
			            text(", writing "), objid(val)]);
		};

		this.read = function(iid, name, val, isGlobal, isScriptLocal) {
			dump_event("read-var", [text("Reading variable " + name + ", yielding "), objid(val)]);
		};

		this.write = function(iid, name, val, lhs, isGlobal, isScriptLocal) {
			dump_event("write-var", [text("Writing variable " + name + ", updating from "), objid(lhs), text(" to "), objid(val)]);
		};

		this._return = function(iid, val) {
			dump_event("return", [text("return ", objid(val))]);
		};

		this._throw = function(iid, val) {
			dump_event("throw", [text("throw ", objid(val))]);
		};

		this.functionEnter = function(iid, f, dis, args) {
			dump_event("enter", [text("entering function "), objid(f),
			            text(" with this="), objid(dis),
			            text(" and argument array "), objid(args)]);
		};

		this.functionExit = function(iid, returnVal, wrappedExceptionVal) {
			dump_event("exit", [text("Exiting function with return value "), objid(returnVal),
			            text(" and exception value "), objid(wrappedExceptionVal)]);
		};

		this.scriptEnter = function(iid, instrumentedFileName, originalFileName) {
			if (!init) {
				init_globals();
				init = true;
			}
			dump_event("script-enter", text("Entering script"));
		};

		this.scriptExit = function(iid, wrappedExceptionVal) {
			dump_event("script-exit", [text("Exiting script with exception value '"), objid(wrappedExceptionVal), text("'")]);
		};

		this.binary = function(iid, op, left, right, result, isOpAssign,
				isSwitchCaseComparison, isComputed) {
			dump_event("op-binary", [text("Evaluating "), objid(left), text(op), objid(right),
			            text(", yielding"), objid(result)]);
		};

		this.unary = function(iid, op, left, result) {
			dump_event("op-unary", [text("Evaluating " + op + " "), objid(left), text(", yielding "), objid(result)]);
		};

		this.conditional = function(iid, result) {
		};

		this.endExpression = function(iid) {
			dump_event("end-expression", text("End of expression"));
		};

		this.endExecution = function() {
			dump_event("end-execution", text("End of execution"));
		};

		this._with = function(iid, val) {
			dump_event("with", [text("with ", objid(val))]);
		};
	}
	sandbox.analysis = new MyAnalysis(this);
})(J$);
