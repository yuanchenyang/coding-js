var w;
var worker_name;

function create_worker() {
    var w = new Worker(worker_name);
    w.onmessage = on_worker_message;
    return w;
}

function switch_scheme() {
    worker_name = "../workers/scheme.js";
    $("#testfile").val("../tests/tests.scm");
    $("#switch-button")
        .val("Switch to Logic")
        .click(switch_logic);
}

function switch_logic() {
    worker_name = "../workers/logic.js";
    $("#testfile").val("../tests/tests.logic");
    $("#switch-button")
        .val("Switch to Scheme")
        .click(switch_scheme);
}

function test_file(filename, output) {
    // Load test cases from specified file
    $.get(filename, function (data) {
        var test_cases = split_cases(data);
        test(test_cases, output);
    });
}

function test(test_cases, output) {
    // Runs the test code in a single global environment.

    var worker = create_worker();
    var eval_result = "";
    var code = "";

    worker.onmessage = function(e) {
        if (e.data.type === "end") {
            check_tests(test_cases, eval_result, output);
            worker.terminate();
            return;
        } else if (e.data.type === "return_value") {
            eval_result += e.data.value + "\n";
        } else if (e.data.type === "displayed_text") {
            eval_result += e.data.value;
        } else if (e.data.type === "error") {
            eval_result += e.data.value + "\n";
        }
    };

    for (var i = 0; i < test_cases.length; i++) {
        if (i > 0) {
            code += '\n(display "TEST_HARNESS")\n';
        }
        code += test_cases[i][0];
    }

    worker.postMessage(code);
}

function check_tests(test_cases, eval_result, out) {
    var code, result, curr_result, result_num_lines;
    var failed = 0;
    var total = test_cases.length;
    var eval_lines = eval_result.split("TEST_HARNESS");

    for (var i = 0; i < test_cases.length; i++) {
        code = test_cases[i][0];
        expected = test_cases[i][1];

        actual = eval_lines[i];

        if (actual !== expected) {
            out.value +=  "\n################\n\nFAILED TEST:" + code +
                "\nEXPECTED:\n" + expected + "\n\GOT:\n" + actual;
            failed += 1;
        }
        eval_lines = eval_lines.slice(result_num_lines);
    }

    out.value += "\nRan "+ total +" test(s). Successful: "+ (total - failed)
         +" Failed: " + failed;
}

function split_cases(code) {
    // Takes in a chunk of code and returns an array containing test cases.
    // Each test case is an array, with its first entry the code to run, and the
    // second entry is the result to compare with.

    var lines = code.split("\n");
    var code_b = "";
    var result_b = "";
    var reading_result = false;
    var test_cases = [];

    for (var i = 0; i < lines.length; i++) {
        var line = lines[i];
        var result_line = (line.slice(0, 9) === "; expect ");

        if (reading_result && (! result_line)) {
            test_cases.push([code_b, result_b]);
            reading_result = false;
            code_b = "";
            result_b = "";
        }

        if (result_line) {
            result_b += line.slice(9) + "\n";
            reading_result = true;
        } else {
            code_b += line + "\n";
        }
    }

    if (reading_result) {
        test_cases.push([code_b, result_b]);
    }

    return test_cases;
}

function on_worker_message(e) {
    if (e.data.type === "end") {
        return;
    } else if (e.data.type === "return_value") {
        output.value += e.data.value + "\n";
    } else if (e.data.type === "displayed_text") {
        output.value += e.data.value;
    } else if (e.data.type === "error") {
        output.value += e.data.value + "\n";
    } else {
        output.value += e.data.value + "\n";
    }
};

$(function() {
    var output = document.getElementById("output");
    $.ajaxSetup({ cache: false });

    $("#eval-button").click(function() {
        w = create_worker();
        output.value = '';
        w.postMessage(this.form.input.value);
    });
    $("#test-button").click(function() {
        output.value = '';
        test_file(this.form.testfile.value, output);
    });
    $("#clear-button").click(function() {
        this.form.input.value = '';
    });
    switch_scheme();
});
