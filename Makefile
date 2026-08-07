# Typecheck the whole tree.  Agda caches interfaces, so this is
# incremental after the first run.
AGDA ?= agda --no-libraries --library-file=$(HOME)/.agda/libraries

.PHONY: check everything clean

check: everything
	cd src && $(AGDA) TheoryGrammar/Everything.agda

# regenerate the import list from the files on disk
everything:
	./gen-everything.sh

clean:
	find . -name '*.agdai' -delete
