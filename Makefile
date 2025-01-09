STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')
LINTING=hlint -i "Use tuple-section"

default:
	stack build
	@cp ${STACKPATH}/bin/issy issy

clean:
	stack clean
	@rm issy

format:
	hindent --line-length 100 src/*/*.hs
	hindent --line-length 100 src/*/*/*.hs
	hindent --line-length 100 src/*/*/*/*.hs
	hindent --line-length 100 src/*/*/*/*/*.hs

lint:
	${LINTING} src/*/*.hs
	${LINTING} src/*/*/*.hs
	${LINTING} src/*/*/*/*.hs
	${LINTING} src/*/*/*/*/*.hs

