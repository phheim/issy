STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')
LINTING=hlint -i "Use tuple-section"

default:
	stack build
	# @mkdir -p builds
	# @cp ${STACKPATH}/bin/* builds/

clean:
	stack clean
	@rm -r builds

format:
	hindent --line-length 100 */*/*.hs
	hindent --line-length 100 */*/*/*.hs
	hindent --line-length 100 */*/*/*/*.hs

lint:
	${LINTING} */*/*.hs
	${LINTING} */*/*/*.hs
	${LINTING} */*/*/*/*.hs

