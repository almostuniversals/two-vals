// Given a list of eligible numbers, spits outs exceptions in that list
// To be called repeatedly on squarefree, then a*p^2, and so on.
function checkEligibility(M, d, S, eligNums, splitTheta, ternPrec)
   // Start timing the process.
   tim := Cputime();
   
   // Compute representability using the approximate boolean theta function on the split local cover
   uncovered := CheckEligibleOnTernary(eligNums, splitTheta, d, ternPrec);
   PrintFile(LOGFILE, Sprintf("There are %o numbers which aren't represented by the ternary form.", #uncovered));
   PrintFile(LOGFILE, Sprintf("They are %o.", uncovered));

   // No exceptions =)
   if #uncovered eq 0 then
      return uncovered;
   end if;

   // Too high exceptions =(
   if Maximum(uncovered) gt 20000 then
      printf "max uncovered=%o is too high, up precision\n", uncovered;
      PrintFile("fixTheseForms.txt", mmm);
      quit;
   end if;
   
   fullLattice := LatticeWithGram(M);
   fullTheta := ComputeTheta(fullLattice, #uncovered eq 0 select 50 else uncovered[1]);
   
   // Compute representability on the actual theta series
   unrepresented := CheckEligibleOnFull(uncovered, fullTheta);
   PrintFile(LOGFILE, Sprintf("The following numbers fail to be represented by the form: %o.", unrepresented));
   
   tim2 := Cputime(tim);
   PrintFile(LOGFILE, Sprintf("Checking eligible numbers complete. Time needed is %o sec.", tim2));

   return unrepresented;
end function;
