

String.prototype.format = function () {
    var o = Array.prototype.slice.call(arguments);
    return this.replace(/{([^{}]*)}/g,
        function (match, capture) {
            var r = o[capture];
            return (typeof r === 'string' || typeof r === 'number') ? r : match;
        }
                       );
};

var CodingJS = (function CodingJS() {
    "use strict";

    return function CodingJSConstructor (interpreter_path, language, cbs) {

        cbs = cbs || {};

        var coding = this;

        coding.config = {interpreter_path: interpreter_path || "",
                         language: language || "scheme",
                         timeout_ms: 30000}; // 30 seconds
        coding.set_interpreter_path = function(path) {
            coding.config.interpreter_path = path;
        };

        coding.set_language = function (language) {
            coding.config.language = language; //TODO: allow mixed languages within page
        };

        coding.focus_callback = cbs.onFocus || function () {};

        coding.clean_code = function (code) {
            //cleans extra newlines that exist to make in-html code look better
            return code.replace(/^\n/, "").replace(/\n*$/, "").replace(/[ \t]*\n/g, "\n").replace(/\s*$/, "");
        };

        coding.$_ = function(s) {
            // lookup element with an id of 's'
            var lookup_str = "[id={0}]".format(s);
            if (lookup_str === "[id={0}]") {
                throw "no s provided";
            }
            var ret = $(lookup_str.replace(/\?/, "\\\?"));
            if (!ret[0]) {
                throw "#" + s + " did coding.not match anything";
            } else {
                return ret;
            }
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.array_eq = function (arr1, arr2) {
            return $(arr1).not(arr2).length == 0 && $(arr2).not(arr1).length == 0;
        };

        coding.shuffle = function (myArray) {
            var i = myArray.length;
            if ( i == 0 ) return false;
            while ( --i ) {
                var j = Math.floor( Math.random() * ( i + 1 ) );
                var tempi = myArray[i];
                var tempj = myArray[j];
                myArray[i] = tempj;
                myArray[j] = tempi;
            }
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.deps_of = {};

        coding.get_deps = function (_editor) {
            if (coding.deps_of[_editor]) {
                return coding.deps_of[_editor];
            } else {
                return [];
            }
        };


        coding.get_depended_on_code = function (_editor) {
            var code = "";

            for (var deps = coding.get_all_deps(_editor), i = 0; i < deps.length; i++) {
                code += coding.editor_of[deps[i]].getValue();
            }

            return code + coding.editor_of[_editor].getValue();
        };

        coding.eval_editor = function (_editor) {

            return coding.eval_scheme(coding.get_depended_on_code(_editor));
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.editor_of = {};

        coding.make_editable = function (_editor) {

            if (coding.editor_of[_editor]) {
                throw "Error: coding.make_editable called with " + _editor + " which already exists!";
            }

            var $editor = coding.$_(_editor);
            if (!$editor) {
                console.log("_editor not found");
                return;
            }
            var code = coding.clean_code($editor.text());

            $editor.empty();

            var editor = CodeMirror($editor[0], {
                'value': code,
                'matchBrackets': true,
                'onFocus': function() {coding.focus_callback(_editor);},
            });

            editor.setOption('extraKeys', {
              'Ctrl-Enter': function() {
                  editor.getOption("onBlur")();
              },
              'Cmd-Enter': function () {
                  editor.getOption("onBlur")();
              }
            });

            coding.editor_of[_editor] = editor;
            return editor;
        };

        coding.link_editor = function (_editor, _output, func) { //sync

            var editor = coding.editor_of[_editor];

            editor.setOption('onBlur', function() {
                if (cbs.onBlur) cbs.onBlur(_editor);
                coding.$_(_output).empty().append($("<span>" + func(_editor, editor.getValue()) + "</span>"));
            });
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.get_all_deps = function(editor_name) {
            var ret = [];
            var marked = [];

            var dfs = function(s) {
                if (marked.indexOf(s) != -1) {
                    return;
                }
                marked.push(s);
                var d = coding.get_deps(s);
                for (var i = 0; i < d.length; i++) {
                    dfs(d[i]);
                }
                if (s != editor_name) {
                    ret.push(s);
                }
            }

            dfs(editor_name);
            return ret;
        };

        coding.get_all_pushes = function(editor_name) {
            var ret = [];

            var dfs = function(s) {
                if (ret.indexOf(s) != -1) {
                    return;
                }
                if (s != editor_name) {
                    ret.push(s);
                }
                var d = coding.get_pushes(s);
                for (var i = 0; i < d.length; i++) {
                    dfs(d[i]);
                }
            }

            dfs(editor_name);
            return ret;
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.pushes_of = {};

        coding.get_pushes = function (_editor) {
            if (coding.pushes_of[_editor]) {
                return coding.pushes_of[_editor];
            } else {
                return [];
            }
        };

        coding.add_dep = function (_e, deps) {
            if (!$.isArray(deps)) {
                throw "deps is coding.not an array: coding.add_dep " + _e;
            }
            coding.deps_of[_e] = deps;
            for (var i in deps) {
                var p = coding.pushes_of[deps[i]];
                if (p) {
                    p.push(_e);
                } else {
                    coding.pushes_of[deps[i]] = [_e];
                }
            }
        };

        ///////////////////////////////////////////////////////////////////////////////

        coding.add_output = function (_e) {
            coding.$_(_e).after($('<div>', {'id': _e + "-output", 'class': "output"}));
        };

        coding.compute = function (s) {
            var def = $.Deferred();

            var output_fragment = [];
            var output = coding.$_(s + "-output");
            var terminated = false;

            var w = new Worker(coding.config.interpreter_path + "workers/" + coding.config.language + ".js");
            w.onmessage = function(e) {
                if (e.data.type === "end") {
                    if (output_fragment.length == 0) {
                        output.empty();
                    }
                    w.terminate();
                    terminated = true;
                    def.resolve();
                    return;
                } else if (e.data.type === "displayed_text") {
                    output_fragment.push($("<span class='output_displayed_text'>" + e.data.value.replace(/\n/g, "<br>") + "</span>"));
                } else if (e.data.type === "return_value") {
                    output_fragment.push($("<span class='output_return_value'>" + e.data.value + "<br> </span>"));
                } else if (e.data.type === "error") {
                    console.log(e.data);
                    output_fragment.push($("<span class='output_error'>" + e.data.value.replace(/\n/g, "<br>") + "</span>"));
                } else {
                    output_fragment.push($("<span>" + e.data + "<br> </span>"));
                }
                output.empty().append(output_fragment);
            };

            function timeout_fn() {
                if (! terminated) {
                    w.terminate();
                    output_fragment.push(
                        $("<span class='output_error'> Computation timed out! </span>"));
                    output.empty().append(output_fragment);
                }
            }

            w.postMessage(coding.get_depended_on_code(s));
            window.setTimeout(timeout_fn, coding.config.timeout_ms);

            return def; //for template code to chain
        };

        /*
         coding.eval_scheme(code).then(function(res) {
            check if res is correct
            update DOM
         });
         */
        coding.eval_scheme = function (code) {

            var def = $.Deferred();

            var w = new Worker(coding.config.interpreter_path + "workers/" + coding.config.language + ".js");
            var out = [];
            w.onmessage = function(e) {
                if (e.data.type === "end") {
                    def.resolve(out); //for .then(function(res)) to catch
                    w.terminate();
                } else {
                    out.push(e.data.value);
                    return;
                }
            };

            w.postMessage(code);

            return def;
        };

        coding.prompt = function (s, deps) {
            if (!s) {
                return;
            }
            coding.make_editable(s).setOption('onBlur', function() {
                for (var pushes = coding.get_all_pushes(s), i = 0; i < pushes.length; i++) {
                    coding.compute(pushes[i]);
                }
                if (cbs.onBlur) cbs.onBlur(s);
                return coding.compute(s);
            });
            coding.add_output(s);
            coding.add_dep(s, (deps || []));
        };

        coding.frozen_prompt = function (s, deps) {
            coding.make_editable(s);
            coding.editor_of[s].setOption("readOnly", 'coding.nocursor');
            coding.editor_of[s].setOption('onBlur', function() {
                // todo: I think this is only needed
                // to run initial code. try to delete it.
                if (cbs.onBlur) cbs.onBlur(s);
                return coding.compute(s);
            });
            coding.add_output(s);
            coding.add_dep(s, (deps || []));
        };

        coding.hidden_prompt = function (s, deps) {
            coding.make_editable(s);
            coding.add_output(s);

            coding.$_(s).hide();
            coding.$_(s + "-output").hide();

            coding.add_dep(s, (deps || []));
        };

        coding.no_output_prompt = function (s, deps) {
            coding.make_editable(s);

            coding.add_dep(s, (deps || []));
        };

        coding.no_output_frozen_prompt = function (s, deps) {
            coding.make_editable(s);
            coding.$_(s).find(".CodeMirror-scroll").addClass("static");
            coding.editor_of[s].setOption("readOnly", 'coding.nocursor');

            coding.add_dep(s, (deps || []));
        };

        coding.make_static = function (_static) { //and coding.no output
            coding.no_output_frozen_prompt(_static);
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.answer = function (s, a) {
            coding.make_static(s);
            coding.$_(s).after($('<div>', {'id': s + "-input", 'class': "input"}));
            coding.make_prompting_input(s + "-input");
            coding.add_output(s + "-input");
            coding.link_editor(s + "-input", s + "-input-output", function(x, y) {
                if (y == a) {
                    return "<div class='right-answer'> \u2713 </div>";
                } else {
                    return "<div class='wrong-answer'> \u2717 </div>";
                }
            });
        };

        coding.equalp_answer = function (s, a) {
            coding.make_static(s);
            coding.$_(s).after($('<div>', {'id': s + "-input", 'class': "input"}));
            coding.make_prompting_input(s + "-input");
            coding.add_output(s + "-input");

            coding.editor_of[s + "-input"].setOption("onBlur", function() {
                var ans = coding.editor_of[s + "-input"].getValue();
                var code = "(equal? (quote {0}) (quote {1}))".format(ans, a);

                coding.eval_scheme(code).then(function(res) {
                    if (res[res.length - 1] === "true\n") {
                        coding.$_(s + "-input-output").empty().append("<div class='right-answer'> \u2713 </div>");
                    } else {
                        coding.$_(s + "-input-output").empty().append("<div class='wrong-answer'> \u2717 </div>");
                    }
                });
                if (cbs.onBlur) cbs.onBlur(s);
            });
        };

        coding.make_prompting_input = function (i) {
            coding.make_change_on_focus_input(i, "'your-input-here", "");
        };

        coding.make_change_on_focus_input = function (i, before, after) {

            coding.make_editable(i);

            var e = coding.editor_of[i];
            e.setValue(before);

            var oldOnFocus = e.getOption("onFocus");
            e.setOption("onFocus", function() {
                oldOnFocus();
                if (e.getValue() == before) {
                    e.setValue(after);
                }
            });
        };

        coding.make_form = function (uid, right_entries, wrong_entries) {

            var form = $('<form>', {'id': uid});

            var entries = [];
            var i;
            for (i in right_entries) {
                entries.push({text: right_entries[i], score: 'right'});
            }
            for (i in wrong_entries) {
                entries.push({text: wrong_entries[i], score: 'wrong'});
            }

            coding.shuffle(entries);

            for (var i in entries) {
                var e = entries[i];
                form.append($("<input>", {type: "checkbox", id: uid + "-" + i, value: e.score}));
                form.append($("<label>", {for: uid + "-" + i, 'html': e.text}));
                form.append($('<br>'));
            }

            return form;
        };

        coding.make_MCQ = function (_mcq, right_entries, wrong_entries) {
            coding.$_(_mcq).append(coding.make_form(_mcq + "_form", right_entries, wrong_entries));

            coding.$_(_mcq).append($("<div>", {'class': 'p-link', 'id': _mcq + "-submit", 'html': 'submit'}));
            coding.add_output(_mcq + "-submit");

            coding.$_(_mcq + "-submit").click(function() {

                var checked = [];
                var unchecked = [];

                coding.$_(_mcq + "_form").children("input:checked").each(function(i, j) {
                    checked.push(j.value);
                });

                coding.$_(_mcq + "_form").children("input:not(:checked)").each(function(i, j) {
                    unchecked.push(j.value);
                });

                var $out = coding.$_(_mcq + "-submit-output");

                console.log(checked);

                if (coding.array_eq(checked,["right"]) && coding.array_eq(unchecked,["wrong"])) {
                    $out.empty().append($("<div class='submit-ans right-answer'> \u2713 </div>"));
                } else {
                    $out.empty().append($("<div class='submit-ans wrong-answer'> \u2717 </div>"));
                }

            });
        };

        ////////////////////////////////////////////////////////////////////////////////

        $(function () {
            var todo = Object.keys(coding.editor_of);

            (function proc() {
                if (todo.length == 0) {
                    if (cbs.onInitialEvalHasCompleted) return cbs.onInitialEvalHasCompleted();
                    return;
                }
                try {
                    var first = todo.shift();
                    coding.editor_of[first].getOption("onBlur")().then(proc);
                } catch (err) {
                    proc();
                }
            })();
        });
    };
})();
