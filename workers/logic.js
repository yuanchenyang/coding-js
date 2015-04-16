// Logic Worker //


importScripts("reader.js", "tokenizer.js", "primitives.js");

onmessage = function(event) {
    var env = create_global_frame();

    var codebuffer = new Buffer(tokenize_lines(event.data.split("\n")));

    while (codebuffer.current() != null) {
        try {
            logic_eval(scheme_read(codebuffer), env);
        } catch(e) {
            this.postMessage({'type': 'error', 'value': e.toString()});
        }
    }
    this.postMessage({"type": "end"});
};


//////////////////
// Environments //
//////////////////

function Frame(parent) {
    this.bindings = {};
    this.parent = parent;
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
    define : function(sym , val) {
        // Define Scheme symbol SYM to have value VAL in THIS
        this.bindings[sym] = val;
    }
};

function lookup(sym, env) {
    // Look up a symbol repeatedly until it is fully resolved.
    try {
        return lookup(env.lookup(sym), env);
    } catch(e) {
        return sym;
    }
}

function ground(expr, env) {
    // Replace all variables with their values in expr.
    if (scheme_symbolp(expr)) {
        var resolved = lookup(expr, env);
        if (expr != resolved) {
            return ground(resolved, env);
        } else {
            return expr;
        }
    } else if (scheme_pairp(expr)) {
        return new Pair(ground(expr.first, env),
                        ground(expr.second, env));
    } else {
        return expr;
    }
}


/////////////////////
// Eval-Apply Loop //
/////////////////////

function do_query(clauses) {
    var query_results = [];
    var grounded = [];
    var vars = get_vars(clauses);
    search(clauses, new Frame(null), 0, query_results);
    query_results.forEach(function (env) {
        var vars_list = [];
        vars.forEach(function (v) {
            vars_list.push([v, ground(v, env)]);
        });
        grounded.push(vars_list);
    });
    return grounded;
}

var DEPTH_LIMIT = 20;
function search(clauses, env, depth, result) {
    // Search for an application of rules to establish all the clauses,
    // non-destructively extending the unifier env.  Limit the search to the
    // nested application of depth rules.
    if (clauses == nil) {
        result.push(env);
    } else if (depth <= DEPTH_LIMIT) {
        facts.forEach(function(fact) {
            fact = rename_variables(fact, get_unique_id());
            var env_head = new Frame(env);
            if (unify(fact.first, clauses.first, env_head)) {
                var env_rules = [];
                search(fact.second, env_head, depth + 1, env_rules);
                env_rules.forEach(function(env_rule) {
                    var results = [];
                    search(clauses.second, env_rule, depth + 1, results);
                    results.forEach(function(r) {
                        result.push(r);
                    });
                });
            }
        });
    }
}

function unify(e, f, env) {
    // Destructively extend env so as to unify (make equal) e and f, returning
    // True if this succeeds and False otherwise.  env may be modified in either
    // case (its existing bindings are never changed).

    e = lookup(e, env);
    f = lookup(f, env);
    if (e == f) {
        return true;
    } else if (isvar(e)) {
        env.define(e, f);
        return true;
    } else if (isvar(f)) {
        env.define(f, e);
        return true;
    } else if (scheme_atomp(e) || scheme_atomp(f)) {
        return false;
    } else {
        return unify(e.first, f.first, env) &&
               unify(e.second, f.second, env);
    }
}

var facts = [];

function logic_eval(expr, env) {
    // Process an input expr, which may be a fact or query.

    if (! scheme_listp(expr)) {
        throw "Error: Expression must be a list: " + expr.toString();
    }

    if (expr.first == "fact" || expr.first == "!") {
        facts.push(expr.second);
    } else if (expr.first == "query" || expr.first == "?") {
        var results = do_query(expr.second);
        var success = false;
        var result_str = [];
        for (var i = 0; i < results.length; i++) {
            if (! success) {
                logic_return("Success!");
            }
            success = true;

            var items = [];
            results[i].forEach(function (e) {
                items.push(e[0].toString().slice(1) + ": " + e[1].toString());
            });
            if (items.length > 0) {
                result_str.push(items.join("\t"));
            }
        }
        if (result_str.length > 0) {
            logic_print(result_str.join("\n"));
        }
        if (! success) {
            logic_return("Failed.");
        }
    } else if (expr.first === "display") {
        logic_print(expr.second.first);
    } else {
        throw "Error: Please! provide a fact or query: " + expr.first;
    }
}


//////////////////////
// Helper Functions //
//////////////////////

function include(arr,obj) {
    return (arr.indexOf(obj) != -1);
}

function get_vars(expr) {
    // Return all logical vars in expr as a list.
    if (isvar(expr)) {
        return [expr];
    } else if (scheme_pairp(expr)) {
        var vs = get_vars(expr.first);
        var second = get_vars(expr.second);
        second.forEach(function (v) {
            if (! include(vs, v)) {
                vs.push(v);
            }
        });
        return vs;
    } else {
        return [];
    }
}

var IDENTIFIER = 0;
function  get_unique_id() {
    //Return a unique identifier.
    IDENTIFIER += 1;
    return IDENTIFIER;
}

function rename_variables(expr, n) {
    // Rename all variables in expr with an identifier N.
    if (isvar(expr)) {
        return expr + "_" + n;
    } else if (scheme_pairp(expr)) {
        return new Pair(rename_variables(expr.first, n),
                        rename_variables(expr.second, n));
    } else {
        return expr;
    }
}

function isvar(symbol) {
    // Return whether symbol is a logical variable.
    return scheme_symbolp(symbol) && symbol[0] == "?";
}

function create_global_frame() {
    // Initialize and return a single-frame environment with built-in names
    var env = new Frame(null);
    return env;
}


function logic_return(val) {
    this.postMessage({'type': "return_value", 'value': val.toString()});
}


function logic_print(val) {
    this.postMessage({'type': "displayed_text", 'value': val.toString() + "\n"});
}


function logic_newline() {
    this.postMessage({'type': "displayed_text", 'value': "\n"});
}
