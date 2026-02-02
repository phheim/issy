STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')
DOCPATH=$(shell stack path | grep local-doc-root | sed 's/local-doc-root: //')
LINTING=hlint -i "Use tuple-section"

default:
	stack build
	@cp ${STACKPATH}/bin/issy issy

clean:
	stack clean
	@rm -f issy
	@rm -f issy-static

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

documentation:
	stack haddock --haddock-internal --only-locals
	@echo ""
	@echo "== Open the following link in your browser =="
	@echo "${DOCPATH}/index.html"

STATIC_DIR=containers/static-build
static:
	@rm -rf ${STATIC_DIR}/build-files/
	mkdir ${STATIC_DIR}/build-files/
	cp -r src ${STATIC_DIR}/build-files/
	cp stack.yaml ${STATIC_DIR}/build-files/
	cp issy.cabal ${STATIC_DIR}/build-files/
	cp Makefile ${STATIC_DIR}/build-files/
	podman build -t issy-static-builder ${STATIC_DIR}/
	@rm -rf ${STATIC_DIR}/build-files/
	${STATIC_DIR}/extract-binary.sh


