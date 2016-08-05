# Two Vals
This repository holds code and log files for the paper ["Classically Integral Quadratic Forms Excepting at Most Two Values,"](http://arxiv.org/abs/1608.01656) by Madeleine Barowsky, William Damron, Andres Mejia, Frederick Saia, Nolan Schock, and Katherine Thompson.

## Quadratic Forms Eligibility Suite
This directory contains all the Magma code we used to run each given form:

*`RunForm.m`---The main source file, containing code to call the rest of the files.
*`RunPrelim.m`---Contains code for computing anisotropic primes, cusp space, local densities, and the cusp and eisenstein coefficients of a given form. Most of this code is courtesy of Jeremy Rouse, who wrote the code initially for the 451 Theorem.
*`Eligibility.m`---Contains functions for computing and checking eligible numbers.
*`CheckEligibility.m`---Contains functions that call `Eligibility.m` to check the eligibility of each number in a given list.
*`RunEligibility.m`---Contains functions that call `Eligibility.m` to generate lists of eligible numbers and subsequently compute their eligibility on `CheckEligibility.m`.


## Log Files
This directory contains one log file (from the Quadratic Forms Eligibility Suite) per the 73 possible excepted pairs and 9 possible excepted singletons proving that each of these forms except exactly that pair or singleton.

Also in this directory is a .zip file containing such log files for every necessary form. (Read at your own risk!)

## Escalations
Included here is an example Sage worksheet file for how we automated the escalation process.
