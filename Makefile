JS_REQ = deps/codemirror/lib/codemirror.js     \
         deps/codemirror/mode/scheme/scheme.js \
         deps/jquery.min.js                    \
         coding.js

CSS_REQ = deps/codemirror/lib/codemirror.css \
          coding.css                         \
          base.css                           \

TARGETS = coding-everything.min.css coding-everything.min.js

all: $(TARGETS)

coding-everything.min.js : $(JS_REQ)
	uglifyjs $^ -o $@ -c

coding-everything.min.css : $(CSS_REQ)
	cat $^ | cleancss -o $@

clean:
	$(RM) $(TARGETS)
