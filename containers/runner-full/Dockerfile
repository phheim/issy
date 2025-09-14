FROM registry.fedoraproject.org/fedora:latest
#@sha256:657562811166c014a3f986414914014b73356254ee97606d2bd68075e652c786

WORKDIR /

# Get Spot
COPY spot.repo spot.repo
RUN dnf config-manager addrepo --from-repofile=spot.repo \
 && dnf -y install spot unzip \
 && dnf -y clean all

# Get Z3
RUN curl -L --output out.zip https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip \
 && unzip out.zip \
 && cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/bin/z3-4.13.3 \
 && rm -r z3-4.13.3-x64-glibc-2.35 out.zip

# Get Issy & internal wrapper
RUN curl -L --output out.zip https://github.com/phheim/issy/releases/download/v1.0-CAV25-AE/issy-v1.0.zip \
 && unzip out.zip \
 && cp issy-v1.0/issy /usr/bin/issy-bin \
 && rm -rf issy-v1.0 

# Build Muval
RUN dnf -y install \
    make \
    automake \
    gcc \
    gcc-c++ \
    kernel-devel \
    flex \
    bison \
    liblas-devel \
    lapack-devel \
    mpfr-devel \
    gmp-devel \
    glpk-devel \
    libffi-devel \
    bc \
    opam \
    pkg-config \
 && dnf -y clean all

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

# Get wrapper scripts
COPY internal-wrapper.sh /usr/bin/issy
COPY call-muval.sh /usr/bin/call-muval
RUN chmod +x /usr/bin/issy  \
 && chmod +x /usr/bin/call-muval
