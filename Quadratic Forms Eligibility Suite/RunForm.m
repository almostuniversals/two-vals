// Runs everything for a given form, in the list of forms
// Correct command line syntax could be:
// magma mmm:=5 RunForm.m

if (not assigned mmm) then
  // Write this error to stdout
  printf "ERROR: script requires mmm to be passed as a command line
  argument.\n";
  printf "This gives the entry in the list of all quaternary
  escalators of the form to preprocess.\n";
  quit;
end if;

if Type(mmm) eq MonStgElt then
   mmm := StringToInteger(mmm);
end if;

LOGFILE := "logs/" cat IntegerToString(mmm) cat ".log";
DATAFILE := "out/" cat IntegerToString(mmm) cat "data.out";
ELIGFILE := "elig/" cat IntegerToString(mmm) cat "elig.out";

// Eligibility.m contains functions to compute/check eligible numbers; clearly it must be
// called before RunEligibility.m and CheckEligibility.m
load "Eligibility.m";
load "RunPrelim.m";
load "CheckEligibility.m";
load "RunEligibility.m";

M, d, S, F4bound, NNNN, chi, aniso := runPrelim();
unrepresented := runEligibility(M, d, S, F4bound, NNNN, chi, aniso);

quit;
