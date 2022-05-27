################### Build Mallob
FROM satcomp-common-base-image
USER root
#  Install required softwares
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y cmake build-essential zlib1g-dev libopenmpi-dev wget unzip build-essential zlib1g-dev cmake python3 build-essential gfortran wget curl

# Build Pkis
# RUN git clone https://ghproxy.com/https://github.com/dezhangxd/taws parkissat
ADD parkissat parkissat
WORKDIR parkissat
RUN make -j