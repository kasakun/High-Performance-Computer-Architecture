# High-Performance-Computer-Architecture

## ForeWord
The prjects are the course projects of CS6290 High Performance Computer Architecture.
Three projects are based on sesc simulator(link) and C++ programming. In each projects, source code of the simulator is modified to realize the requirement. 

The benchmark used is Splash 2.

## Environment Setting
To implement the simulator, compile it.
Use command:
```
cd
$ make 
```



## Project 1 Branch Prediction

Raytrace Benchmark is used in this project to test the sesc branch prediction.
Part 3 requires the program to count the execution number of each branch prediction. Instructions are classified into four groups according to exe times of each(1-9, 10-99, 100-999, 1000+).

The modified part in Bpred.h and Bpred.cpp is clearly marked as `//My code`.

The output count format is:
Group | Group exe times | Group correct times | Number of Instructions


## Project 2
Cache Misses

## Project 3
Coherence Misses and 3C