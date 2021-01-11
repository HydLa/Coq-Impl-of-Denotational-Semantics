FROM ubuntu

# install opam
RUN apt-get update \
    && apt-get -y install opam m4
RUN opam init -y \
    && eval `opam config env`

# install coq
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install coq

# install coqide
RUN opam depext conf-pkg-config.1.1 \
    && opam depext conf-gtksourceview.2
RUN opam install coqide
ENV OPAMROOT=~/.opam

# install ssreflect if necessary
# RUN opam install coq-mathcomp-ssreflect

# setting for GUI
RUN apt-get install -y libx11-dev
ENV DISPLAY=host.docker.internal:0.0

WORKDIR /work
ENTRYPOINT eval `opam config env` && coqide
