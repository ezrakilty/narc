all:
	ghc --make Narc -odir build -hidir build

docs:
	haddock Narc -h -o docs

clean:
	find build -name "*.o" -exec rm {} \;
	find build -name "*.hi" -exec rm {} \;

clean-docs:
	rm docs/*

.PHONY: all docs clean clean-docs
