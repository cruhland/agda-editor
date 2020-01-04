SOURCES := $(shell find . -type f -name '*.agda')

agda-editor: $(SOURCES)
	agda -c --ghc-flag=-dynamic --ghc-flag=-o --ghc-flag=agda-editor src/Editor.agda

.PHONY: clean
clean:
	rm -f agda-editor
	rm -rf src/MAlonzo
	find . -type f -name '*.agdai' -exec rm '{}' \;
