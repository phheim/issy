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

COPY internal-wrapper.sh /usr/bin/issy
RUN chmod +x /usr/bin/issy
