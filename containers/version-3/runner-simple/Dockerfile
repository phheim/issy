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
RUN chmod +x /usr/bin/issy

ENTRYPOINT ["/usr/bin/issy"]
