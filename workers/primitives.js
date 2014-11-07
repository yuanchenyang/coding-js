//PRIMITIVES.JS//

// This file implements the primitives of the Scheme language

function PrimitiveProcedure(fn, use_env, varargs) {
    this.fn = fn;
    this.use_env = use_env || false;
    this.varargs = varargs || false;
}

PrimitiveProcedure.prototype = {
    toString : function() {return "PrimitiveProcedure";}
};

function check_type(val, predicate, k, name) {
    // Returns VAL.  Raises a SchemeError if not PREDICATE(VAL)
    // using "argument K of NAME" to describe the offending value
    if (! predicate(val)) {
        throw "SchemeError: argument "+ k + " of "+ name +
            " has wrong type ("+ typeof val +")";
    }
    return val;
}

function scheme_tostring(val) {
    if (val instanceof SchemeString) {
        return val.str;
    }
    return val.toString();
}

var _PRIMITIVES = {};

function scheme_booleanp(x) {
    return (x === true) || (x === false);
}
_PRIMITIVES["boolean?"] = new PrimitiveProcedure(scheme_booleanp);

function scheme_true(val) {
    // All values in Scheme are true except False.
    return (!(val === false));
}

function scheme_false(val) {
    // Only False is false in Scheme
    return (val === false);
}

function scheme_not(x) {
    return ! scheme_true(x);
}
_PRIMITIVES["not"] = new PrimitiveProcedure(scheme_not);

function scheme_eqp(x, y) {
    if (scheme_stringp(x) && scheme_stringp(y)) {
        return x.toString() === y.toString(); //is this correct?
    }
    return x == y;
}
_PRIMITIVES["eq?"] = new PrimitiveProcedure(scheme_eqp);

function scheme_equalp(x, y) {
    return x.toString() === y.toString();
}
_PRIMITIVES["equal?"] = new PrimitiveProcedure(scheme_equalp);

function scheme_pairp(x) {
    return x instanceof Pair;
}
_PRIMITIVES["pair?"] = new PrimitiveProcedure(scheme_pairp);

function scheme_nullp(x) {
    return x === nil;
}
_PRIMITIVES["null?"] = new PrimitiveProcedure(scheme_nullp);

function scheme_listp(x) {
    // Return whether x is a well-formed list. Assumes no cycles
    while (x !== nil) {
        if (!(x instanceof Pair)) {
            return false;
        }
        x = x.second;
    }
    return true;
}
_PRIMITIVES["list?"] = new PrimitiveProcedure(scheme_listp);

function scheme_length(x) {
    check_type(x, scheme_listp, 0, "length");
    return x.length;
}
_PRIMITIVES["length"] = new PrimitiveProcedure(scheme_length);

function scheme_cons(x, y) {
    return new Pair(x, y);
}
_PRIMITIVES["cons"] = new PrimitiveProcedure(scheme_cons);

function scheme_car(x) {
    check_type(x, scheme_pairp, 0, 'car');
    return x.first;
}
_PRIMITIVES["car"] = new PrimitiveProcedure(scheme_car);

function scheme_cdr(x) {
    check_type(x, scheme_pairp, 0, 'cdr');
    return x.second;
}
_PRIMITIVES["cdr"] = new PrimitiveProcedure(scheme_cdr);

var _CXRS = ["caar", "cadr", "cdar", "cddr", "caaar", "caadr", "cadar", "caddr",
             "cdaar", "cdadr", "cddar", "cdddr", "caaaar", "caaadr", "caadar",
             "caaddr", "cadaar", "cadadr", "caddar", "cadddr", "cdaaar", "cdaadr",
             "cdadar", "cdaddr", "cddaar", "cddadr", "cdddar", "cddddr"];
function scheme_cxr(form) {
    return function(exp) {
        for (var i = form.length - 2; i > 0; i--) {
            if (form[i] == 'a') {
                exp = scheme_car(exp);
            } else {
                exp = scheme_cdr(exp);
            }
        }
        return exp;
    };
}

_CXRS.forEach(function(form) {
    _PRIMITIVES[form] = new PrimitiveProcedure(scheme_cxr(form));
});

function scheme_list() {
    var result = nil;
    for (var i = arguments.length - 1; i >= 0; i--) {
        result = new Pair(arguments[i], result);
    }
    return result;
}
_PRIMITIVES["list"] = new PrimitiveProcedure(scheme_list, false, true);
function scheme_append() {
    if (arguments.length == 0) {
        return nil;
    }
    var result = arguments[arguments.length - 1];
    for (var i = arguments.length - 2; i >= 0; i--) {
        var v = arguments[i];
        if (v !== nil) {
            check_type(v, scheme_pairp, i, "append");
            var r = new Pair(v.first, result);
            var p = r;
            var v = v.second;
            while (scheme_pairp(v)) {
                p.second = new Pair(v.first, result);
                p = p.second;
                v = v.second;
            }
            result = r;
        }
    }
    return result;
}
_PRIMITIVES["append"] = new PrimitiveProcedure(scheme_append, false, true);

function scheme_symbolp(x) {
    return typeof x === "string";
}
_PRIMITIVES["symbol?"] = new PrimitiveProcedure(scheme_symbolp);

function scheme_stringp(x) {
    return x instanceof SchemeString;
}
_PRIMITIVES["string?"] = new PrimitiveProcedure(scheme_stringp);

function scheme_numberp(x) {
    return typeof x.valueOf() === "number";
}
_PRIMITIVES["number?"] = new PrimitiveProcedure(scheme_numberp);

function scheme_integerp(x) {
    return (typeof x.valueOf() === "number") && Math.floor(x) == x.valueOf();
}
_PRIMITIVES["integer?"] = new PrimitiveProcedure(scheme_integerp);

function _check_nums(vals) {
    // Check that all elements in array VALS are numbers
    for (var i = 0; i < vals.length; i++) {
        if (! scheme_numberp(vals[i])) {
            throw "SchemeError: operand '"+ vals[i].toString() +"' is not a number";
        }
    }
}

function _arith(fn, init, vals) {
    // Perform the fn function on the number values of VALS, with INIT as
    // the value when VALS is empty. Returns the result as a Scheme value
    _check_nums(vals);
    _check_nums([init]);
    var s = init;
    for (var i = 0; i < vals.length; i++) {
        s = fn(s, vals[i]);
    }
    if (Math.round(s) === s) {
        s = Math.round(s);
    }
    return s;
}

function scheme_add() {
    return _arith(function(a, b) {return a+b;}, 0, arguments);
}
_PRIMITIVES["+"] = new PrimitiveProcedure(scheme_add, false, true);

function scheme_sub() {
    var args = Array.prototype.slice.call(arguments);
    if (args.length < 1) {
        throw "SchemeError: too few args";
    } else if (args.length == 1) {
        _check_nums([args[0]]);
        return -args[0];
    } else {
        return _arith(function(a, b) {return a-b;}, args[0],
                      args.slice(1));
    }
}
_PRIMITIVES["-"] = new PrimitiveProcedure(scheme_sub, false, true);

function scheme_mul() {
    return _arith(function(a, b) {return a*b;}, 1, arguments);
}
_PRIMITIVES["*"] = new PrimitiveProcedure(scheme_mul, false, true);

function scheme_div(x, y) {
    if (y === 0) {
        throw "SchemeError: division by zero";
    }
    return _arith(function(a, b) {return a/b;}, x, [y]);
}
_PRIMITIVES["/"] = new PrimitiveProcedure(scheme_div);

function scheme_quotient(x, y) {
    var d = x/y;
    return Math[d > 0 ? "floor" : "ceil"](d); //round to zero
}
_PRIMITIVES["quotient"] = new PrimitiveProcedure(scheme_quotient);

function scheme_random(n) {
    return Math.floor((Math.random()*n));
}
_PRIMITIVES["random"] = new PrimitiveProcedure(scheme_random);

_PRIMITIVES["abs"] = new PrimitiveProcedure(Math.abs);
_PRIMITIVES["log"] = new PrimitiveProcedure(Math.log);
_PRIMITIVES["exp"] = new PrimitiveProcedure(Math.exp);
_PRIMITIVES["expt"] = new PrimitiveProcedure(Math.pow);
_PRIMITIVES["sin"] = new PrimitiveProcedure(Math.sin);
_PRIMITIVES["cos"] = new PrimitiveProcedure(Math.cos);
_PRIMITIVES["tan"] = new PrimitiveProcedure(Math.tan);
_PRIMITIVES["asin"] = new PrimitiveProcedure(Math.asin);
_PRIMITIVES["acos"] = new PrimitiveProcedure(Math.acos);

//TODO: two-argument version
_PRIMITIVES["atan"] = new PrimitiveProcedure(Math.atan);

function scheme_remainder(x, y) {
    return  x % y;
}
_PRIMITIVES["remainder"] = new PrimitiveProcedure(scheme_remainder);

function scheme_modulo(x, y) {
    return ((x % y) + y) % y;
}
_PRIMITIVES["modulo"] = new PrimitiveProcedure(scheme_modulo);

function scheme_floor(x) {
    _check_nums([x]);
    return Math.floor(x);
}
_PRIMITIVES["floor"] = new PrimitiveProcedure(scheme_floor);

function scheme_ceil(x) {
    _check_nums([x]);
    return Math.ceil(x);
}
_PRIMITIVES["ceil"] = new PrimitiveProcedure(scheme_ceil);


function scheme_eq(x, y) {
    _check_nums([x, y]);
    return x.valueOf() === y.valueOf();
}
_PRIMITIVES["="] = new PrimitiveProcedure(scheme_eq);

function scheme_lt(x, y) {
    _check_nums([x, y]);
    return x < y;
}
_PRIMITIVES["<"] = new PrimitiveProcedure(scheme_lt);

function scheme_gt(x, y) {
    _check_nums([x, y]);
    return x > y;
}
_PRIMITIVES[">"] = new PrimitiveProcedure(scheme_gt);

function scheme_le(x, y) {
    _check_nums([x, y]);
    return x <= y;
}
_PRIMITIVES["<="] = new PrimitiveProcedure(scheme_le);

function scheme_ge(x, y) {
    _check_nums([x, y]);
    return x >= y;
}
_PRIMITIVES[">="] = new PrimitiveProcedure(scheme_ge);

function scheme_evenp(x) {
    _check_nums([x]);
    return x % 2 === 0;
}
_PRIMITIVES["even?"] = new PrimitiveProcedure(scheme_evenp);

function scheme_oddp(x) {
    _check_nums([x]);
    return x % 2 === 1;
}
_PRIMITIVES["odd?"] = new PrimitiveProcedure(scheme_oddp);

function scheme_zerop(x) {
    _check_nums([x]);
    return x === 0;
}
_PRIMITIVES["zero?"] = new PrimitiveProcedure(scheme_zerop);

function scheme_atomp(x) {
    return scheme_booleanp(x) || scheme_numberp(x) || scheme_symbolp(x) ||
        scheme_nullp(x) || scheme_stringp(x);
}
_PRIMITIVES["atom?"] = new PrimitiveProcedure(scheme_atomp);

function _check_strings(strings) {
    var x;
    for (var i = 0; i < strings.length; i++) {
        x = strings[i];
        if (! scheme_stringp(x)) {
            throw "SchemeError: " + x + " is not a string";
        }
    }
}

function scheme_string_append() {
    _check_strings(arguments);
    var s = '';
    for (var i = 0; i < arguments.length; i++) {
        s += arguments[i].str;
    }
    return s;
}
_PRIMITIVES["string-append"] = new PrimitiveProcedure(scheme_string_append, false, true);

function scheme_string_ref(s, k) {
    _check_strings([s]);
    _check_nums([k]);
    return s.getchar(k);
}
_PRIMITIVES["string-ref"] = new PrimitiveProcedure(scheme_string_ref);

function scheme_string_length(s) {
    _check_strings([s]);
    return s.length;
}
_PRIMITIVES["string-length"] = new PrimitiveProcedure(scheme_string_length);

function scheme_substring(s, start, end) {
    _check_strings([s]);
    _check_nums([start, end]);
    return s.substring(start, end);
}
_PRIMITIVES["substring"] = new PrimitiveProcedure(scheme_substring);

function scheme_display(val) {
    this.postMessage({'type': "displayed_text", 'value': scheme_tostring(val)});
}
_PRIMITIVES["display"] = new PrimitiveProcedure(scheme_display);

function scheme_print(val) {
    this.postMessage({'type': "displayed_text",
                      'value': scheme_tostring(val) + "\n"});
}
_PRIMITIVES["print"] = new PrimitiveProcedure(scheme_print);

function scheme_newline() {
    this.postMessage({'type': "displayed_text", 'value': "\n"});
}
_PRIMITIVES["newline"] = new PrimitiveProcedure(scheme_newline);

function scheme_error(msg) {
    if (msg === undefined) {
        throw "SchemeError";
    } else {
        throw "SchemeError: " + msg;
    }
}
_PRIMITIVES["error"] = new PrimitiveProcedure(scheme_error);

function runtime() {
    // Returns the number of miliseconds from Jan 1 1970
    // Not a good way of measuring runtime of a program though
    return new Date().getTime();
}
_PRIMITIVES["runtime"] =
    new PrimitiveProcedure(runtime);

function scheme_exit() {
    throw "EOFError";
}
_PRIMITIVES["exit"] = new PrimitiveProcedure(scheme_exit);
