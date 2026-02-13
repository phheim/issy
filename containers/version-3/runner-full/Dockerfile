FROM ubuntu:24.04@sha256:3afff29dffbc200d202546dc6c4f614edc3b109691e7ab4aa23d02b42ba86790

WORKDIR /

# Dependencies
RUN apt-get update \
 && apt-get install -y \
    build-essential \
    g++ \
    curl \
    unzip \
    libgmp-dev \
    libffi-dev \
 && apt-get clean

# Build Spot
RUN curl -L --output spot-2.12.2.tar.gz  http://www.lrde.epita.fr/dload/spot/spot-2.12.2.tar.gz \
 && tar xf spot-2.12.2.tar.gz \
 && rm spot-2.12.2.tar.gz \
 # Building & Installation \
 && cd spot-2.12.2 \
 && ./configure --prefix /usr --disable-python \
 && make \
 && make install \
 # Cleanup \
 && make clean \
 && cd ..

# Dependencies (MuVal)
RUN apt-get update \
 && apt-get install -y \
    libblas-dev \
    liblapack-dev \
    libmpfr-dev \
    libglpk-dev \
    bc \
    opam \
    pkg-config \
 && apt-get clean

# Build MuVal
RUN opam init --disable-sandboxing \
 && opam switch create 5.2.0 \
 && opam install dune 

RUN curl -L --output out.zip https://github.com/hiroshi-unno/coar/archive/1d49999975b00f1430b3c9d10b90ab00b561e836.zip \
 && unzip out.zip \
 && rm -f out.zip \
 && mv coar-1d49999975b00f1430b3c9d10b90ab00b561e836 /muval

WORKDIR /muval

RUN eval $(opam env) && opam install . --deps-only  --confirm-level=yes
RUN eval $(opam env) && dune build main.exe

WORKDIR /

# Get Z3 (4.15.1)
RUN curl -L --output out.zip https://github.com/Z3Prover/z3/releases/download/z3-4.15.1/z3-4.15.1-x64-glibc-2.39.zip \
 && unzip out.zip \
 && cp z3-4.15.1-x64-glibc-2.39/bin/z3 /usr/bin/z3-4.15.1 \
 && rm -r z3-4.15.1-x64-glibc-2.39 out.zip

# Get Issy
RUN curl -L --output out.zip https://github.com/phheim/issy/releases/download/v3.0/issy-v3.zip \
 && unzip out.zip \
 && cp issy-v3/issy /usr/bin/issy-bin \
 && rm -rf issy-v3

# Get wrapper scripts
COPY internal-wrapper.sh /usr/bin/issy
COPY call-muval.sh /usr/bin/call-muval
RUN chmod +x /usr/bin/issy  \
 && chmod +x /usr/bin/call-muval

ENTRYPOINT ["/usr/bin/issy"]
