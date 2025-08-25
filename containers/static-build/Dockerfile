FROM alpine@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1

# Root setup
WORKDIR /
RUN apk add \
    curl git binutils-gold curl gcc g++ \
    gmp-static gmp-dev libc-dev libffi-dev make musl-dev ncurses-dev perl tar xz

# User setup
RUN adduser -D user
USER user
RUN mkdir /home/user/build
WORKDIR /home/user/build

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh 

# 
# First pseudo-build to setup Compiler & Co
#
COPY --chown=user init-build init-build
RUN source /home/user/.ghcup/env \
 && cd init-build \
 && stack build \
 && cd .. \
 && rm -rf init-build 

#
# Build Issy
#
COPY build-files/src/ src/
COPY build-files/stack.yaml stack.yaml
COPY build-files/issy.cabal issy.cabal
COPY build-files/Makefile Makefile
RUN source /home/user/.ghcup/env \
 && sed -i 's/^-----optl-static/    -optl-static/' issy.cabal \
 && make
