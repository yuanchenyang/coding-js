// This interpreter is based on the Scheme interpreter project for UC Berkeley
// CS61A course. The starter code and description for the project can be found
// at this webpage:
//
// http://www-inst.eecs.berkeley.edu/~cs61a/fa12/projects/scheme/scheme.html
//
// The resulting python code after completing the project is then translated
// into JavaScript by me (Chenyang Yuan).


// Scheme Worker //

importScripts("reader.js", "tokenizer.js", "primitives.js");

onmessage = function(event) {
    var env = create_global_frame();

    var codebuffer = new Buffer(tokenize_lines(event.data.split("\n")));

    var evalstack = [];

    while (codebuffer.current() != null) {
        try {
            var result = scheme_eval(scheme_read(codebuffer), env);
            if (! (result === null || result === undefined)) {
                this.postMessage({'type': 'return_value', 'value': result.toString()});
            }
        } catch(e) {
            var estring = e.toString() + '\n\nCurrent Eval Stack:\n' +
                '-------------------------\n' + print_stack(env.stack);
            this.postMessage({
                'type': 'error',
                'value': estring
            });
        }
    }
    this.postMessage({'type': 'end'});
};

function print_stack(stack) {
    var ret = "";
    stack.reverse();
    stack.forEach(function (e,i) {
        ret += i.toString() + ":\t" + e.toString() + "\n";
    })
    return ret;
}

//SCHEME.JS//


// This file implements the core Scheme interpreter functions, including the
// eval/apply mutual recurrence, environment model, and read-eval-print loop


/////////////////////
// Data Structures //
/////////////////////

function Frame(parent) {
    this.bindings = {};
    this.parent = parent;
    // All child frames' stacks point to the stack of the global parent frame
    if (parent != null) {
        this.stack = parent.stack;
    }
}
Frame.prototype = {
    lookup : function(symbol) {
        // Return the value bound to SYMBOL.  Errors if SYMBOL is not found
        if (symbol in this.bindings) {
            return this.bindings[symbol];
        } else if (this.parent !== null) {
            return this.parent.lookup(symbol);
        } else {
            throw "SchemeError: unknown identifier: " + symbol.toString();
        }
    },
    global_frame : function() {
        // The global environment at the root of the parent chain
        var e = this;
        while (e.parent !== null) {
            e = e.parent;
        }
        return e;
        },
    make_call_frame : function(formals, vals, dotted) {
        // Return a new local frame whose parent is THIS, in which the symbols
        // in the Scheme formal parameter list FORMALS are bound to the Scheme
        // values in the Scheme value list VALS. If optional DOTTED is true,
        // any extra values will be bound to the dotted symbol in FORMALS.

        var frame = new Frame(this);
        vals = pair_to_array(vals);
        if (dotted) {
            var list, last;
            if (scheme_symbolp(formals)) {
                list = nil;
                last = formals;
            } else {
                var a = formals.seperate_dotted();
                list = a[0];
                last = a[1];
            }
            var non_dotted_length = list.length;
            var rest = array_to_pair(vals.slice(non_dotted_length));
            formals = scheme_append(list, new Pair(last, nil));
            vals = vals.slice(0, non_dotted_length);
            vals.push(rest);
        }
        formals = pair_to_array(formals);
        if (formals.length != vals.length) {
            throw "SchemeError: Invalid number of arguments";
        }
        for (var i = 0; i < formals.length; i++) {
            frame.bindings[formals[i]] = vals[i];
        }
        return frame;
        },
    define : function(sym , val) {
        // Define Scheme symbol SYM to have value VAL in THIS
        this.bindings[sym] = val;
    },
    sete : function(sym, val) {
        // Locates the binding of SYM in the first frame in the environment
        // that contains a binding for SYM and changes that binding to VAL.
        // Returns an error if SYM does not exist in all frames.
        if (sym in this.bindings) {
            this.bindings[sym] = val;
        } else if (this.parent !== null) {
            this.parent.sete(sym, val);
        } else {
            throw "SchemeError: " + sym.toString() + " not found!";
        }
    }
};

function SetContinuation(target, env) {
    // (set! target val)

    this.target = target;
    this.env = env;
}

function SetCarContinuation(rval, env) {
    // (set-car! target val)

    this.rval = rval;
    this.env = env;
}

function SetCdrContinuation(rval, env) {
    // (set-cdr! target val)

    this.rval = rval;
    this.env = env;
}

function BeginContinuation(exprs, env) {
    // (begin val ,@exprs)

    this.exprs = exprs;
    this.env = env;
}

function DefineContinuation(target, env) {
    // (define target val)

    this.target = target;
    this.env = env;

}

function CondContinuation(consq, clauses, env) {
    // (cond [(val consq) ,@clauses ])

    this.consq = consq;
    this.clauses = clauses;
    this.env = env;
}

function IfContinuation(consq, altnt, env) {
    // (if val consq altnt)

    this.consq = consq;
    this.altnt = altnt;
    this.env = env;
}

function AndContinuation(args, env) {
    // (and val ,@args)

    this.args = args;
    this.env = env;
}

function OrContinuation(args, env) {
    // (or val ,@args)

    this.args = args;
    this.env = env;
}

function AppContinuation(args, pos, env) {
    // (val ,@args)
    // if this.f is defined:
    // (f args[0] args[1] ... args[pos-1] val args[pos+1] ...)

    this.args = args;
    this.pos = pos;
    this.env = env;
}

// A procedure defined by a lambda expression or the complex define form
function LambdaProcedure(formals, body, env, dotted) {
    // A procedure whose formal parameter list is FORMALS (a Scheme list or a
    // one with a dotted last symbol), whose body is a single Scheme expression
    // BODY, and whose parent environment is the Frame ENV. DOTTED is true if
    // extra parameters need to be passed. A lambda expression containing
    // multiple expressions, such as (lambda (x) (display x) (+ x 1)) can be
    // handled by using (begin (display x) (+ x 1)) as the body
    this.formals = formals;
    this.body = body;
    this.env = env;
    this.dotted = dotted;
}

LambdaProcedure.prototype = {
    toString : function() {
        return "(lambda "+ this.formals.toString() +" "+
               this.body.toString() +")" ;
    }
};

/////////////////////
// Eval-Apply Loop //
/////////////////////

function apply_cont(conts, val) {

    // console.log("apply", conts, val.toString());

    if (conts.length === 0) {
        return val;
    }

    var cont = conts[0];
    if (cont instanceof AppContinuation) {

        // args is a scheme list

        if (cont.pos !== -1) {
            cont.args.setitem(cont.pos, val);
        } else {
            cont.f = val;
        }

        if (cont.pos == -1 && cont.args.length > 0) {
            cont.pos++;
            return scheme_eval_k(cont.args.getitem(cont.pos), cont.env, conts);
        } else if (cont.pos < cont.args.length - 1) {
            cont.pos++;
            return scheme_eval_k(cont.args.getitem(cont.pos), cont.env, conts);
        } else {

            var args = cont.args;
            var procedure = cont.f;

            if (procedure instanceof LambdaProcedure) {
                env = procedure.env.make_call_frame(procedure.formals, args,
                                                    procedure.dotted);
                expr = procedure.body;
                env.stack.pop();

                return scheme_eval_k(procedure.body, env, conts.slice(1));

            } else if (procedure instanceof PrimitiveProcedure) {
                cont.env.stack.pop();
                return apply_cont(conts.slice(1),
                    apply_primitive(procedure, args, cont.env));
            } else {
                throw "SchemeError: Cannot call " + procedure.toString();
            }
        }
    } else if (cont instanceof IfContinuation) {
        var pred = val;

        cont.env.stack.pop();

        if (scheme_true(pred)) {
            return scheme_eval_k(cont.consq, cont.env, conts.slice(1));
        } else {
            return scheme_eval_k(cont.altnt, cont.env, conts.slice(1));
        }
    } else if (cont instanceof AndContinuation) {
        if (scheme_false(val)) {
            return apply_cont(conts.slice(1), false);
        } else if (cont.args.length === 0) {
            return apply_cont(conts.slice(1), val);
        } else {
            var newcont = new AndContinuation(cont.args.second, cont.env);
            return scheme_eval_k(cont.args.first, cont.env, [newcont].concat(conts.slice(1)));
        }
    } else if (cont instanceof OrContinuation) {
        if (!scheme_false(val)) {
            return apply_cont(conts.slice(1), val);
        } else if (cont.args.length === 0) {
            return apply_cont(conts.slice(1), false);
        } else {
            var newcont = new OrContinuation(cont.args.second, cont.env);
            return scheme_eval_k(cont.args.first, cont.env, [newcont].concat(conts.slice(1)));
        }
    } else if (cont instanceof SetContinuation) {

        var target = cont.target;
        if (scheme_symbolp(target)) {
            cont.env.sete(target, val);
        } else {
            throw "SchemeError: cannot set!: " + target.toString()
                + " is not a variable";
        }

        cont.env.stack.pop();
        return apply_cont(conts.slice(1), undefined);

    } else if (cont instanceof SetCarContinuation) {

        if (cont.target) {
            cont.target.first = val;
            return apply_cont(conts.slice(1), undefined);
        } else {
            cont.target = val;
            return scheme_eval_k(cont.rval, cont.env, conts);
        }
    } else if (cont instanceof SetCdrContinuation) {

        if (cont.target) {
            cont.target.second = val;
            return apply_cont(conts.slice(1), undefined);
        } else {
            cont.target = val;
            return scheme_eval_k(cont.rval, cont.env, conts);
        }
    } else if (cont instanceof BeginContinuation) {
        if (cont.exprs.length === 0) {
            return apply_cont(conts.slice(1), val);
        } else {
            var newcont = new BeginContinuation(cont.exprs.second, cont.env);
            return scheme_eval_k(cont.exprs.first, cont.env, [newcont].concat(conts.slice(1)));
        }
    } else if (cont instanceof DefineContinuation) {

        cont.env.define(cont.target, val);
        return apply_cont(conts.slice(1), undefined);

    } else if (cont instanceof CondContinuation) {

        if (scheme_true(val)) {
            if (cont.consq.length === 0) {
                return apply_cont(conts.slice(1), val);
            } else {
                var ret = new Pair('begin', cont.consq)
                return scheme_eval_k(ret, cont.env, conts.slice(1));
            }
        } else if (cont.clauses.length === 0) {
            return apply_cont(conts.slice(1), undefined);
        } else {
            var newcont = new CondContinuation(cont.clauses.getitem(0).second, cont.clauses.second, cont.env);
            return scheme_eval_k(cont.clauses.getitem(0).first, cont.env, [newcont].concat(conts.slice(1)));
        }
    }

    // return val;
}

function scheme_eval(expr, env) {
    return scheme_eval_k(expr, env, []);
}

function scheme_eval_k(expr, env, conts) {
    // Evaluate Scheme expression EXPR in environment ENV
    // After that, apply the continuation CONTS

    // console.log("eval", expr.toString(), conts);

    env.stack.push(expr);
    var result;

    if (expr === null) {
        throw 'SchemeError: Cannot evaluate an undefined expression.';
    }
    // Evaluate Atoms
    if (scheme_symbolp(expr)) {
        env.stack.pop();
        return apply_cont(conts, env.lookup(expr));
    } else if (scheme_atomp(expr)) {
        env.stack.pop();
        return apply_cont(conts, expr);
    }
    if (! scheme_listp(expr)) {
        throw "SchemeError: malformed list: " + expr.toString();
    }
    var first = expr.first;
    var rest = expr.second;

    if (first === 'if') {
        return do_if_form(rest, env, conts);
    } else if (first === 'and') {
        return do_and_form(rest, env, conts);
    } else if (first === 'or') {
        return do_or_form(rest, env, conts);
    } else if (first === 'begin') {
        return do_begin_form(rest, env, conts);
    } else if (first === 'lambda') {
        env.stack.pop();
        res = make_lambda(rest, env);
        return apply_cont(conts, res);
    } else if (first === 'set!') {
        return do_sete_form(rest, env, conts);
    } else if (first === 'set-car!') {
        return do_set_care_form(rest, env, conts);
    } else if (first === 'set-cdr!') {
        return do_set_cdre_form(rest, env, conts);
    } else if (first === 'quote') {
        return do_quote_form(rest, env, conts);
    } else if (first === 'define') {
        env.stack.pop();
        return do_define_form(rest, env, conts);
    } else if (first === 'cond') {
        return do_cond_form(rest, env, conts);
    // ok
    } else if (first === 'let') {
        var l = do_let_form(rest, env);
        expr = l[0];
        env = l[1];
        env.stack.pop();
        return scheme_eval_k(expr, env, conts);
    } else {
        var new_cont = new AppContinuation(rest.copy(), -1, env);
        return scheme_eval_k(first, env, [new_cont].concat(conts));
    }
    return result;
}

function scheme_apply(procedure, args, env) {
    // Apply Scheme PROCEDURE to argument values ARGS in environment ENV

    if (procedure instanceof PrimitiveProcedure) {
        return apply_primitive(procedure, args, env);
    } else if (procedure instanceof LambdaProcedure) {
        var call_frame = procedure.env.make_call_frame(procedure.formals, args,
                                                       procedure.dotted);
        return scheme_eval(procedure.body, call_frame);
    } else {
        throw "SchemeError: Cannot call " + procedure.toString();
    }
}

function apply_primitive(procedure, args, env) {
    // Apply PrimitiveProcedure PROCEDURE to a Scheme list of ARGS in ENV
    var fn = procedure.fn;
    args = pair_to_array(args);
    if (procedure.use_env) {
        args.push(env);
    }
    // Errors if expected arguments does not match
    if (fn.length != args.length && ! procedure.varargs) {
        throw "SchemeError: Expected " + fn.length +
              " arguments, got " + args.length;
    }
    return procedure.fn.apply(this, args);
}

function num_parameters(func) {
    // Returns the number of formal parameters a function has
    var funStr = func.toString();
    var args = funStr.slice(funStr.indexOf('(')+1, funStr.indexOf(')'));
    return args.match(/,/g).length + 1;
}

function pair_to_array(list) {
    // Helper function to turn a scheme list into a javascript array
    if (list === nil) {
        return [];
    }
    return [list.first].concat(pair_to_array(list.second));
}

function array_to_pair(array) {
    // Reverses the output of pair_to_array
    if (array.length == 0) {
        return nil;
    } else {
        var first = array.shift();
        return new Pair(first, array_to_pair(array));
    }
}


///////////////////
// Special Forms //
///////////////////

function make_lambda(vals, env) {
    // Evaluate a lambda form with parameters VALS in environment ENV
    var value, formals;
    formals = vals.getitem(0);
    var dotted = check_formals(formals);
    if (vals.length == 2) {
        value = vals.getitem(1);
    } else {
        value = new Pair('begin', vals.second);
    }
    return new LambdaProcedure(formals, value, env, dotted);
}

function do_sete_form(vals, env, conts) {
    // Evaluate a set! form with parameters VALS in environment ENV
    var target, value;
    check_form(vals, 2, 2);
    target = vals.getitem(0);

    var newcont = new SetContinuation(target, env);
    return scheme_eval_k(vals.getitem(1), env, [newcont].concat(conts));
}

function do_set_care_form(vals, env, conts) {
    // Evaluate a set-car! form with parameters VALS in environment ENV
    var target, value;
    check_form(vals, 2, 2);

    target = vals.getitem(0);

    var newcont = new SetCarContinuation(vals.getitem(1), env);
    return scheme_eval_k(target, env, [newcont].concat(conts));
}

function do_set_cdre_form(vals, env, conts) {
    // Evaluate a set-cdr! form with parameters VALS in environment ENV
    var target, value;
    check_form(vals, 2, 2);

    target = vals.getitem(0);

    var newcont = new SetCdrContinuation(vals.getitem(1), env);
    return scheme_eval_k(target, env, [newcont].concat(conts));
}

function do_define_form(vals, env, conts) {
    // Evaluate a define form with parameters VALS in environment ENV
    var target, value, t, v;
    check_form(vals, 2);
    target = vals.getitem(0);
    if (scheme_symbolp(target)) {
        check_form(vals, 2, 2);
        var newcont = new DefineContinuation(target, env);
        return scheme_eval_k(vals.getitem(1), env, [newcont].concat(conts));
    } else if (target instanceof Pair) {
        t = target.getitem(0);
        if (! scheme_symbolp(t)) {
            throw "SchemeError: not a variable: " + t.toString();
        }
        v = new Pair(vals.first.second, vals.second);
        value = make_lambda(v, env);
        env.define(t, value);
        return apply_cont(conts, undefined);
    } else {
        throw "SchemeError: bad argument to define";
    }
}

function do_quote_form(vals, env, conts) {
    // Evaluate a quote form with parameters VALS
    check_form(vals, 1, 1);
    env.stack.pop();
    return apply_cont(conts, vals.getitem(0));

}

function do_let_form(vals, env) {
    // Evaluate a let form with parameters VALS in environment ENV

    check_form(vals, 2);
    var bindings = vals.getitem(0);
    if (! scheme_listp(bindings)) {
        throw "SchemeError: bad bindings list in let form";
    }
    for (var i = 0; i < bindings.length; i++) {
        var binding = bindings.getitem(i);
        check_form(binding, 2, 2);
        if (! scheme_symbolp(binding.getitem(0))) {
            throw "SchemeError: bad binding: " + binding.toString();
        }
    }

    var bindings = vals.getitem(0);
    var exprs = vals.second;
    // Add a frame containing bindings
    var new_env = env.make_call_frame(nil, nil);
    for (var i = 0; i < bindings.length; i++) {
        var binding = bindings.getitem(i);
        var name = binding.getitem(0);
        var value = scheme_eval(binding.getitem(1), env);
        new_env.define(name, value);
    }
    // Evaluate all but the last expression after bindings, and return the last
    var last = exprs.length - 1;
    for (i = 0; i < last; i++) {
        scheme_eval(exprs.getitem(i), new_env);
    }
    return [exprs.getitem(last), new_env];
}

/////////////////
// Logic Forms //
/////////////////

function do_if_form(vals, env, conts) {
    // Evaluate if form with parameters VALS in environment ENV
    check_form(vals, 3, 3);

    var newcont = new IfContinuation(vals.getitem(1), vals.getitem(2), env);
    return scheme_eval_k(vals.getitem(0), env, [newcont].concat(conts));
}

function do_and_form(vals, env, conts) {
    // Evaluate short-circuited and with parameters VALS in environment ENV
    var newcont = new AndContinuation(vals.copy(), env);
    return scheme_eval_k(true, env, [newcont].concat(conts));
}

function do_or_form(vals, env, conts) {
    // Evaluate short-circuited or with parameters VALS in environment ENV
    var newcont = new OrContinuation(vals.copy(), env);
    return scheme_eval_k(false, env, [newcont].concat(conts));
}

function do_cond_form(vals, env, conts) {
    // Evaluate cond form with parameters VALS in environment ENV

    var newvals = vals.copy();
    for (var i = 0; i < newvals.length; i++) {
        var clause = newvals.getitem(i);
        check_form(clause, 1);

        if (clause.first === "else") {
            clause.first = true;
            if (i < newvals.length - 1) {
                throw "SchemeError: else must be last";
            }
            if (clause.second === nil) {
                throw "SchemeError: badly formed else clause";
            }
        }
    }


    var newcont = new CondContinuation(nil, vals, env);
    return scheme_eval_k(false, env, [newcont].concat(conts));

    // var test;
    // for (var i = 0; i < vals.length; i++) {
    //     var clause = vals.getitem(i);
    //     if (clause.first === "else") {
    //         test = true;
    //     } else {
    //         test = scheme_eval(clause.first, env);
    //     }
    //     if (scheme_true(test)) {
    //         if (clause.second.length == 0) {return test;}
    //         return new Pair('begin', clause.second);
    //     }
    // }
    // return null;
}

function do_begin_form(vals, env, conts) {
    // Evaluate begin form with parameters VALS in environment ENV
    check_form(vals, 1);

    var newcont = new BeginContinuation(vals.second.copy(), env);
    return scheme_eval_k(vals.first, env, [newcont].concat(conts));
}

//////////////////////
// Helper Functions //
//////////////////////

function create_global_frame() {
    // Initialize and return a single-frame environment with built-in names
    var env = new Frame(null);
    env.define("eval", new PrimitiveProcedure(scheme_eval, true));
    env.define("apply", new PrimitiveProcedure(scheme_apply, true));
    env.stack = [];
    add_primitives(env);
    return env;
}

function add_primitives(frame) {
    for (var name in _PRIMITIVES) {
        frame.define(name, _PRIMITIVES[name]);
    }
}

// Utility methods for checking the structure of Scheme programs

function check_form(expr, min, max) {
    // Check EXPR is a proper list whose length is at least MIN and no more than
    // MAX (default: no maximum). Raises a SchemeError if this is not the case
    if (! scheme_listp(expr)) {
        throw "SchemeError: badly formed expression: " + expr.toString();
    }
    var length = expr.length;
    if (length < min) {
        throw "SchemeError: too few operands in form, expr=" + expr.toString();
    } else if ( (! (max === undefined)) && (length > max) ) {
        throw "SchemeError: too many operands in form: " + expr.toString();
    }
}

function check_formals(formals) {
    // Check that FORMALS is a valid parameter list, a Scheme list of symbols
    // in which each symbol is distinct.
    // FORMALS can also be a single symbol.
    // Returns false when FORMALS is a well-formed list. Return true otherwise.

    var last;
    var symbols = [];

    if (scheme_symbolp(formals)) {
        return true;
    }

    if (! scheme_listp(formals)) {
        var a = formals.seperate_dotted();
        formals = a[0];
        last = a[1];
    }

    check_form(formals, 0);
    for (var i = 0; i < formals.length; i++) {
        var symbol = formals.getitem(i);
        check_symbol(symbol, symbols);
        symbols.push(symbol);
    }

    if (last !== undefined) {
        check_symbol(last, symbols);
        return true;
    } else {
        return false;
    }
}

function check_symbol(symbol, symbols) {
    if (! scheme_symbolp(symbol)) {
        throw "SchemeError: not a symbol: " + symbol.toString();
    }
    if (symbols.inside(symbol)) {
        throw "SchemeError: repeated symbol in formal parameters: "
            + symbol;
    }
}
