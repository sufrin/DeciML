PARSER=exprParser
STEM=$(PARSER)Messages


default:: $(STEM).default;  cp  $(STEM).default $(STEM).ml
diff::  $(STEM).new $(STEM);  diff $(STEM).new $(STEM)
ml::    $(STEM).ml
new::   $(STEM).new
raw::   $(STEM).raw

cp::     $(STEM).new; cp  $(STEM).new $(STEM)
cpraw::  $(STEM).raw; cp  $(STEM).raw $(STEM)
       
       
$(STEM).raw: $(PARSER).mly;\
        menhir --canonical --list-errors $(PARSER).mly > $(STEM).raw

$(STEM).new: $(PARSER).mly $(STEM);\
        menhir --canonical --update-errors $(STEM) $(PARSER).mly > $(STEM).new 

$(STEM).ml: $(PARSER).mly $(STEM);\
        menhir --canonical $(PARSER).mly --compile-errors $(STEM) > $(STEM).ml
        
$(STEM): $(PARSER).mly; @\
         [ -f $(STEM) ] || (echo "*** $(STEM) doesn't exist"; echo "*** make and edit $(STEM).raw, then make cpraw ml"; exit 1)

.PHONY: new raw diff ml

listing: ; listing -c -p tests/*.dml expr.ml value.ml main.ml parsing.ml utils.ml exprParser.mly exprLexer.ml syntaxrole.ml





