"use strict";


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

    return function CodingJSConstructor (interpreter_path, language) {

        var coding = this;

        coding.config = {interpreter_path: interpreter_path || "",
                         language: language || "scheme"};
        coding.set_interpreter_path = function(path) {
            coding.config.interpreter_path = path;
        };

        coding.set_language = function (language) {
            coding.config.language = language; //TODO: allow mixed languages within page
        };

        coding.focus_callback = function () {
            //for clients to override
        };

        coding.cleanCode = function (code) {
            //cleans extra newlines that exist to make in-html code look better
            return code.replace(/^\n/, "").replace(/\n*$/, "").replace(/[ \t]*\n/g, "\n").replace(/\s*$/, "");
        };

        coding.$_ = function(s) {
            // lookup element with an id of 's'
            var ret = $("[id={0}]".format(s).replace(/\?/, "\\\?"));
            if (!ret[0]) {
                throw "#" + s + " did coding.not match anything";
            } else {
                return ret;
            }
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.arrayEq = function (arr1, arr2) {
            return $(arr1).not(arr2).length == 0 && $(arr2).not(arr1).length == 0;
        };

        coding.isArray = function (o) {
            return Object.prototype.toString.call(o) === '[object Array]';
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

        coding.depsOf = {};

        coding.getDeps = function (_editor) {
            if (coding.depsOf[_editor]) {
                return coding.depsOf[_editor];
            } else {
                return [];
            }
        };


        coding.getDependedOnCode = function (_editor) {
            var code = "";

            for (var deps = coding.getDeps(_editor), i = 0; i < deps.length; i++) {
                code += coding.getDependedOnCode(deps[i]);
            }

            return code + coding.editorOf[_editor].getValue();
        };

        coding.eval_editor = function (_editor) {

            return coding.eval_scheme(coding.getDependedOnCode(_editor));
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.editorOf = {};

        coding.makeEditable = function (_editor) {

            if (coding.editorOf[_editor]) {
                throw "Error: coding.makeEditable called with " + _editor + " which already exists!";
            }

            var $editor = coding.$_(_editor);
            var code = coding.cleanCode($editor.text());

            $editor.empty();

            var editor = CodeMirror($editor[0], {
                'value': code,
                'matchBrackets': true,
                'onFocus': function() {console.log("focus_callback" + _editor); coding.focus_callback(_editor);}
            });

            editor.setOption('extraKeys', {'Ctrl-Enter': function() {
                editor.getOption("onBlur")();
            }});

            coding.editorOf[_editor] = editor;
            return editor;
        };

        coding.linkEditor = function (_editor, _output, func) { //sync

            var editor = coding.editorOf[_editor];

            editor.setOption('onBlur', function() {
                coding.$_(_output).empty().append($("<span>" + func(_editor, editor.getValue()) + "</span>"));
            });
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.getAllDeps = function (s) {
            var ret = [];
            for (var i = 0, d = coding.getDeps(s); i < d.length; i++) {
                ret = ret.concat(coding.getAllDeps(d[i]));
                ret.push(d[i]);
            }
            return ret;
        };

        coding.getAllPushes = function (s) {
            var ret = [];
            for (var i = 0, d = coding.getPushes(s); i < d.length; i++) {
                ret.push(d[i]);
                ret = ret.concat(coding.getAllPushes(d[i]));
            }
            return ret;
        };

        coding.focus_callback = function (s) {
            var ts = "";
            for (var i = 0, d = coding.getAllDeps(s); i < d.length; i++) {  //TODO list all deps
                ts += coding.editorOf[d[i]].getValue() + "\n\n";
            }

            ts += "<b>" + coding.editorOf[s].getValue() + "</b>";

            $("#currently-editing").html("<pre>" + ts + "</pre>");
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.pushesOf = {};

        coding.getPushes = function (_editor) {
            if (coding.pushesOf[_editor]) {
                return coding.pushesOf[_editor];
            } else {
                return [];
            }
        };

        coding.addDep = function (_e, deps) {
            if (!$.isArray(deps)) {
                throw "deps is coding.not an array: coding.addDep " + _e;
            }
            coding.depsOf[_e] = deps;
            for (var i in deps) {
                var p = coding.pushesOf[deps[i]];
                if (p) {
                    p.push(_e);
                } else {
                    coding.pushesOf[deps[i]] = [_e];
                }
            }
        };

        ///////////////////////////////////////////////////////////////////////////////

        coding.addOutput = function (_e) {
            coding.$_(_e).after($('<div>', {'id': _e + "-output", 'class': "output"}));
        };

        coding.compute = function (s) {
            var def = $.Deferred();

            var _output = s + "-output";
            var output_fragment = [];

            var w = new Worker(coding.config.interpreter_path + "workers/" + coding.config.language + ".js");
            w.onmessage = function(e) {
                if (e.data.type === "end") {
                    if (output_fragment.length == 0) {
                        coding.$_(_output).empty();
                    }
                    w.terminate();
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
                coding.$_(_output).empty().append(output_fragment);
            };

            w.postMessage(coding.getDependedOnCode(s));

            for (var pushes = coding.getPushes(s), i = 0; i < pushes.length; i++) {
                coding.compute(pushes[i]);
            }
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

            console.log(code);
            w.postMessage(code);

            return def;
        };

        coding.prompt = function (s, deps) {
            coding.makeEditable(s).setOption('onBlur', function() {
                return coding.compute(s);
            });
            coding.addOutput(s);
            coding.addDep(s, (deps || []));

        };

        coding.frozen_prompt = function (s, deps) {
            coding.makeEditable(s);
            coding.editorOf[s].setOption("readOnly", 'coding.nocursor');
            coding.editorOf[s].setOption('onBlur', function() {
                return coding.compute(s);
            });
            coding.addOutput(s);
            coding.addDep(s, (deps || []));
        };

        coding.hidden_prompt = function (s, deps) {
            coding.makeEditable(s);
            coding.addOutput(s);

            coding.$_(s).hide();
            coding.$_(s + "-output").hide();

            coding.addDep(s, (deps || []));
        };

        coding.no_output_prompt = function (s, deps) {
            coding.makeEditable(s);

            coding.addDep(s, (deps || []));
        };

        coding.no_output_frozen_prompt = function (s, deps) {
            coding.makeEditable(s);
            coding.$_(s).find(".CodeMirror-scroll").addClass("static");
            coding.editorOf[s].setOption("readOnly", 'coding.nocursor');

            coding.addDep(s, (deps || []));
        };

        coding.makeStatic = function (_static) { //and coding.no output
            coding.no_output_frozen_prompt(_static);
        };

        ////////////////////////////////////////////////////////////////////////////////

        coding.answer = function (s, a) {
            coding.makeStatic(s);
            coding.$_(s).after($('<div>', {'id': s + "-input", 'class': "input"}));
            coding.makePromptingInput(s + "-input");
            coding.addOutput(s + "-input");
            coding.linkEditor(s + "-input", s + "-input-output", function(x, y) {
                if (y == a) {
                    return "<div class='right-answer'> \u2713 </div>";
                } else {
                    return "<div class='wrong-answer'> \u2717 </div>";
                }
            });
        };

        coding.equalp_answer = function (s, a) {
            coding.makeStatic(s);
            coding.$_(s).after($('<div>', {'id': s + "-input", 'class': "input"}));
            coding.makePromptingInput(s + "-input");
            coding.addOutput(s + "-input");

            coding.editorOf[s + "-input"].setOption("onBlur", function() {
                var ans = coding.editorOf[s + "-input"].getValue();
                var code = "(equal? (quote {0}) (quote {1}))".format(ans, a);

                coding.eval_scheme(code).then(function(res) {
                    if (res[res.length - 1] === "true\n") {
                        coding.$_(s + "-input-output").empty().append("<div class='right-answer'> \u2713 </div>");
                    } else {
                        coding.$_(s + "-input-output").empty().append("<div class='wrong-answer'> \u2717 </div>");
                    }
                });
            });
        };

        coding.makePromptingInput = function (i) {
            coding.makeChangeOnFocusInput(i, "'your-input-here", "");
        };

        coding.makeChangeOnFocusInput = function (i, before, after) {

            coding.makeEditable(i);

            var e = coding.editorOf[i];
            e.setValue(before);

            var oldOnFocus = e.getOption("onFocus");
            e.setOption("onFocus", function() {
                oldOnFocus();
                if (e.getValue() == before) {
                    e.setValue(after);
                }
            });
        };

        coding.makeForm = function (uid, right_entries, wrong_entries) {

            var form = $('<form>', {'id': uid});

            var entries = [];
            var i;
            for (i in right_entries) {
                entries.push({text: right_entries[i], score: 'right'});
            }
            for (i in wrong_entries) {
                entries.push({text: wrong_entries[i], score: 'wrong'});
            }

            shuffle(entries);

            for (var i in entries) {
                var e = entries[i];
                form.append($("<input>", {type: "checkbox", id: uid + "-" + i, value: e.score}));
                form.append($("<label>", {for: uid + "-" + i, 'html': e.text}));
                form.append($('<br>'));
            }

            return form;
        };

        coding.makeMCQ = function (_mcq, right_entries, wrong_entries) {
            coding.$_(_mcq).append(coding.makeForm(_mcq + "_form", right_entries, wrong_entries));

            coding.$_(_mcq).append($("<div>", {'class': 'p-link', 'id': _mcq + "-submit", 'html': 'submit'}));
            coding.addOutput(_mcq + "-submit");

            coding.$_(_mcq + "-submit").click(function() {

                var checked = [];
                var unchecked = [];

                coding.$_(_mcq + "_form").children("input:checked").each(function(i, j) {
                    checked.push(j.value);
                });

                coding.$_(_mcq + "_form").children("input:coding.not(:checked)").each(function(i, j) {
                    unchecked.push(j.value);
                });

                var $out = coding.$_(_mcq + "-submit-output");

                console.log(checked);

                if (coding.arrayEq(checked,["right"]) && coding.arrayEq(unchecked,["wrong"])) {
                    $out.empty().append($("<div class='submit-ans right-answer'> \u2713 </div>"));
                } else {
                    $out.empty().append($("<div class='submit-ans wrong-answer'> \u2717 </div>"));
                }

            });
        };

        ////////////////////////////////////////////////////////////////////////////////
        coding.createTOC = function () {
            $("h3, h4").each(function(i) {

                var current = $(this);

                var title = current.text().slice(0,50).replace(/^\s+/, "").replace(/\s+$/, "").replace(/:/, "").replace(/\s+/g, "-").replace(/\./g, "-").replace(/\-+/g, "-").replace(/[\(\)]/g, "").replace(/\?/, "").replace(/'/g, "");

                current.attr("id", title);

                var a = $("<a>", {href: "#" + title, html: current.text().slice(0,50), 'class': current[0].coding.nodeName.toLowerCase()});

                a.click(function() {
                    $('html, body').animate({
                        'scrollTop':   $('#' + title).offset().top
                    }, 250);
                });

                $("#toc").append(a).append($('<br>'));
            });

            $('#sidebox').animate({'right':'0%'});
        };
        $(function () {
            var todo = Object.keys(coding.editorOf);

            (function proc() {
                if (todo.length == 0) {
                    return;
                }
                try {
                    var first = todo.shift();
                    coding.editorOf[first].getOption("onBlur")().then(proc);
                } catch (err) {
                    proc();
                }
            })();
        });
    };
})();
