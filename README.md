# ParKissat
ParKissat is short for Parallel-Kissat.
For more details, please refer our SAT Competition 2022 document.

This repository contains Three Dockerfiles that build the ParKissat parallel solver using the SAT-Comp 2022 infrastructure.
For more details about the structure, please see [https://github.com/aws-samples/aws-batch-comp-infrastructure-sample](https://github.com/aws-samples/aws-batch-comp-infrastructure-sample)
and [https://github.com/aws-samples/aws-satcomp-solver-sample](https://github.com/aws-samples/aws-satcomp-solver-sample) for help.
ParKissat are built on the top of the base containers satcomp-base:leader and satcomp-base:worker. Thus, please follow the steps in the `aws-batch-comp-infrastructure-sample` repository up to the point at which the base containers have been built.  

## How to Build

To build the ParKissat base container: 

1. Navigate to the `base` subdirectory.
2. Run `docker build -t parkissat-base .`

To build the ParKissat leader container: 

1. Navigate to the `leader` subdirectory.
2. Run `docker build -t parkissat:leader .`

To build the ParKissat worker container: 
(useless in fact, just keep the same with the framework)
1. Navigate to the `worker` subdirectory.
2. Run `docker build -t parkissat:worker .`

After building both images, run `docker image ls` and make sure you see both `parkissat:leader` and `parkissat:worker` in the list of images.

## Note

ParKissat are parallel solver, rather than distributed solver. Please set the number of worker to 0.


If you want to build and use on linux directly:

1. Navigate to the `base/parkissat` subdirectory.
2. Run `make -j`
3. Use `./run_pakis.sh [cnf_file]`
