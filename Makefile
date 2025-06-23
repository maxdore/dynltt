AGDA = agda

all:
	$(AGDA) Everything.agda
	$(AGDA) Axiomatic.agda

html:
	$(AGDA) --html --html-dir=html Everything.agda
	$(AGDA) --html --html-dir=html Axiomatic.agda

clean:
	rm -rf html
	rm -rf _build
	rm -f *.agdai
	rm -f .DS_Store
