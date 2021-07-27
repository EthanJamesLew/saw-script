#!/usr/bin/env bash
set -xe

export TESTS=$1
if [ "$2" ]; then
    export S2N_LIBCRYPTO=$2
fi

cd /saw-script/s2n
echo 'JOBS=1' >> codebuild/bin/jobs.sh
source codebuild/bin/s2n_setup_env.sh
SAW=true SAW_INSTALL_DIR=tmp-saw codebuild/bin/s2n_install_test_dependencies.sh
cp /saw-bin/saw "$SAW_INSTALL_DIR"/bin/saw
cp /saw-bin/abc "$SAW_INSTALL_DIR"/bin/abc
ldd "$SAW_INSTALL_DIR"/bin/saw
"$SAW_INSTALL_DIR"/bin/saw --version
ldd "$SAW_INSTALL_DIR"/bin/abc
exec codebuild/bin/s2n_codebuild.sh
