// Must be called after RunPrelim.m or loading the data.out file.
// Computes the eligible primes and numbers

// These repConds functions determine if a number has unbounded divisibility at an anisotropic prime

function repConds1(num)
   if num mod 3 eq 0 then
      if ((num div 2) mod 9 eq 0) or (num gt 7 and (num div 7) mod 3 eq 0) or (num gt 11 and (num div 11) mod 3 eq 0) or ((num mod 9) eq 0) then
         num;
         return true;
      end if;
   end if;
   return false;
end function;

function repConds2(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 1;
end function;

function repConds3(num)
   fact := Factorization(num);
   if #fact eq 1 and fact[1][1] eq 5 and fact[1][2] mod 2 eq 1 then
      return true;
   end if;
   if #fact eq 2 and fact[1] eq <4,1> and fact[2][1] eq 5 and fact[2][2] mod 2 eq 1 then
      return true;
   end if;
   return false;
end function;

function repConds4(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 0 and fact[2] eq <3,1>;
end function;

function repConds5(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      if fact[1] eq <2,1> then
         return fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
      end if;
      return (fact[2] eq <7,1> or fact[2] eq <11,1>) and fact[1][1] eq 3 and fact[1][2] mod 2 eq 1;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[3] eq <7,1> and fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
   end if;
   return false;
end function;

function repConds6(num)
   fact := Factorization(num);
   if #fact eq 1 and fact[1][1] eq 17 then
      return true;
   end if;
   if #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 17 then
      return true;
   end if;
   return false;
end function;

function repConds7(num)
   fact := Factorization(num);
   if #fact eq 2 then
      if fact[1][1] eq 5 and fact[1][2] mod 2 eq 0 and fact[2] eq <17,1> then 
         return true;
      end if;
      if  (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 5 and fact[2][2] mod 2 eq 0 then
         return true;
      end if;
   end if;
   return false;
end function;

function repConds8(num)
   fact := Factorization(num);
   if #fact eq 2 then
      if (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 5 and fact[2][2] mod 2 eq 0 then
         return true;
      end if;
   end if;
   return false;
end function;

function repConds9(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 13;
   end if;
   if #fact eq 2 then
      return (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 13;
   end if;
   if #fact eq 3 then 
      return fact[1] eq <2,1> and fact[2] eq <3,1> and fact[3][1] eq 13;
   end if;
   return false;
end function;

function repConds10(num)
   fact := Factorization(num);
   if #fact eq 2 then
      return fact[1] eq <3,1> and fact[2][1] eq 7;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <3,1> and fact[3][1] eq 7;
   end if;
   return false;
end function;

function repConds11(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 11;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 11;
   end if;
   return false;
end function;

function repConds12(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
end function;

function repConds13(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,2> and fact[2][1] eq 3;
   end if;
   return false;
end function;

function repConds14(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 3 and fact[2][2] mod 2 eq 1;
end function;

function repConds15(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 2;
end function;

function repConds16(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 1 and fact[2] eq <3,1>;
end function;

function repConds17(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 5 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      if fact[1] eq <2,1> then
         return fact[2][1] eq 5 and fact[2][2] mod 2 eq 0;
      end if;
      return fact[1][1] eq 5 and fact[1][2] mod 2 eq 1 and fact[2] eq <7,1>;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[3] eq <7,1> and fact[2][1] eq 5 and fact[2][2] mod 2 eq 1;
   end if;
   return false;
end function;

function repConds18(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return (fact[1][1] eq 3) and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1][1] eq 2 and (fact[1][2] eq 2 or fact[1][2] eq 4) and fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
   end if;
   return false;
end function;

function repConds19(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 11;
end function;

function repConds20(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 7 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      if fact[1] eq <5,1> then
         return fact[2][1] eq 7 and fact[2][2] mod 2 eq 1;
      end if;
      if fact[1] eq <3,1> then
         return fact[2][1] eq 7 and fact[2][2] mod 2 eq 0;
      end if;
      return (fact[1][1] eq 7 and fact[1][2] mod 2 eq 1 and fact[2] eq <13,1>) or fact[1][1] eq 7 and fact[1][2] mod 2 eq 0 and fact[2] eq <47,1>;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <5,1> and fact[3][1] eq 7;
   end if;
   return false;
end function;

function repConds21(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 3;
end function;

function repConds22(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 0;
end function;

function repConds23(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 5 and fact[1][2] mod 2 eq 1;
end function;

function repConds24(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 13;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 13;
   end if;
   return false;
end function;

function repConds25(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 1;
   end if;
   if #fact eq 2 then
      if fact[1] eq <2,1> then
         return fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
      end if;
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 1 and fact[2] eq <13,1>;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2][1] eq 3 and (fact[3] eq <5,1> or fact[3] eq <17,1>);
   end if;
   return false;
end function;

function repConds26(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 1;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
   end if;
   return false;
end function;

function repConds27(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 1 and fact[2] eq <5,1>;
end function;

function repConds28(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 5 and fact[1][2] mod 2 eq 0;
end function;

function repConds29(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 1 and fact[2] eq <7,1>;
end function;

function repConds30(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 0;
end function;

function repConds31(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 3 and fact[1][2] mod 2 eq 1;
end function;

function repConds32(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 5 and fact[2][2] mod 2 eq 0;
end function;

function repConds33(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <2,1> and fact[2][1] eq 5 and fact[2][2] mod 2 eq 1;
end function;

function repConds34(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 1;
   end if;
   if #fact eq 2 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0 and fact[2][1] eq 3 and fact[2][2] mod 2 eq 1;
   end if;
   return false;
end function;

function repConds35(num)
   fact := Factorization(num);
   return #fact eq 2 and fact[1] eq <5,1> and fact[2][1] eq 7;
end function;

function repConds36(num)
   fact := Factorization(num);
   return #fact eq 2 and (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 5 and fact[2][2] mod 2 eq 1;
end function;

function repConds37(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 7;
   end if;
   if #fact eq 2 then
      return (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 7;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <3,1> and fact[3][1] eq 7;
   end if;
   return false;
end function;

function repConds38(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 5;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 5;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <3,1> and fact[3][1] eq 5;
   end if;
   return false;
end function;

function repConds39(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 7;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 7;
   end if;
   return false;
end function;

function repConds40(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0 and fact[2] eq <13,1>;
   end if;
   return false;
end function;

function repConds41(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,2> and fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
   end if;
   return false;
end function;

function repConds42(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 17;
   end if;
   if #fact eq 2 then
      return (fact[1] eq <2,1> or fact[1] eq <3,1> or fact[1] eq <11,1>) and fact[2][1] eq 17;
   end if;
   if #fact eq 3 then
      return (fact[1] eq <2,1>) and (fact[2] eq <3,1> or fact[2] eq <11,1>) and fact[3][1] eq 17;
   end if;
   return false;
end function;

function repConds43(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 5 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      if fact[1] eq <3,1> then
         return fact[2][1] eq 5 and fact[2][2] mod 2 eq 0;
      end if;
      return fact[1][1] eq 5 and fact[1][2] mod 2 eq 1 and fact[2] eq <7,1>;
   end if;
   return false;
end function;

function repConds44(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 13 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return (fact[1] eq <2,1> or fact[1] eq <3,1>) and fact[2][1] eq 13;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <3,1> and fact[3][1] eq 13;
   end if;
   return false;
end function;

function repConds45(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 0 and fact[2] eq <13,1>;
   end if;
   return false;
end function;

function repConds46(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 19;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,1> and fact[2][1] eq 19;
   end if;
   return false;
end function;

function repConds47(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0 and fact[2] eq <13,1>;
   end if;
   if #fact eq 3 then
      return fact[1][1] eq 2 and fact[1][2] mod 2 eq 0 and fact[2] eq <3,1> and (fact[3] eq <5,1> or fact[3] eq <13,1>);
   end if;
   return false;
end function;

function repConds48(num)
   fact := Factorization(num);
   return #fact eq 2 and (fact[1] eq <2,1> or fact[1] eq <5,1>) and fact[2][1] eq 17;
end function;

function repConds49(num)
   fact := Factorization(num);
   return #fact eq 2 and (fact[1][1] eq 2 and fact[1][2] mod 2 eq 1) and fact[2] eq <5,1>;
end function;

function repConds50(num)
   fact := Factorization(num);
   if #fact eq 2 then
      if fact[1] eq <2,1> then
         return fact[2][1] eq 3 and fact[2][2] mod 2 eq 0;
      end if;
      return fact[1][1] eq 3 and fact[1][2] mod 2 eq 0 and fact[2] eq <5,1>;
   end if;
   return false;
end function;

function repCondsPt2Num19(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 2 and fact[1][2] mod 2 eq 0;
end function;

function repCondsPt3(num)
   fact := Factorization(num);
   if #fact eq 1 then
      return fact[1][1] eq 5 and fact[1][2] mod 2 eq 0;
   end if;
   if #fact eq 2 then
      return fact[1] eq <2,2> and fact[2][1] eq 5 and fact[2][2] mod 2 eq 0;
   end if;
   return false;
end function;

function repCondsPt4(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 5;
end function;

function repCondsPt5(num)
   fact := Factorization(num);
   return #fact eq 1 and fact[1][1] eq 3 and fact[1][2] mod 2 eq 0;
end function;

function repCondsActual5(num)
   fact := Factorization(num);
   if #fact eq 2 then
      if fact[1][1] eq 5 then
         return fact[1][2] mod 2 eq 1 and fact[2] eq <17,1>;
      else
         return fact[2][1] eq 5 and fact[2][1] mod 2 eq 1 and (fact[1] eq <2,1> or fact[1] eq <3,1>); 
      end if;
   end if;
   return false;
end function;

function repCondsPt6(num)
   fact := Factorization(num);
   if #fact eq 2 then
      return fact[1] eq <5,1> and fact[2][1] eq 13;
   end if;
   if #fact eq 3 then
      return fact[1] eq <2,1> and fact[2] eq <5,1> and fact[3][1] eq 13;
   end if;
   return false;
end function;

// This computes eligible primes, squarefree eligible numbers, square eligible numbers from those, and so on.
// I would like to acknowledge that this code is poorly written
function runEligibility(M, d, S, F4bound, NNNN, chi, aniso)
   // Start timing
   tim := Cputime();
   
   fullLattice := LatticeWithGram(M);
   
   primeBound := GetEligPrimesBound(F4bound, NNNN, chi, aniso);
   PrintFile(LOGFILE, Sprintf("The bound for eligible primes is %o.", primeBound));
   PrintFile(ELIGFILE, Sprintf("primeBound := %o;", primeBound));
   
   eligPrimes := GetEligiblePrimes(primeBound, NNNN, chi, aniso);
   PrintFile(LOGFILE, Sprintf("There are %o eligible primes.", #eligPrimes));
   PrintFile(ELIGFILE, Sprintf("eligPrimes := %o;", eligPrimes));
   
   maxNumPrimeProduct := GetMaxNumPrimes(eligPrimes, F4bound);
   PrintFile(LOGFILE, Sprintf("The product of more than %o primes exceeds the bound.", maxNumPrimeProduct));
   PrintFile(ELIGFILE, Sprintf("maxNumPrimeProduct := %o;", maxNumPrimeProduct));
   
   eligFromPrimes := EligibleFromPrimes(F4bound, eligPrimes, maxNumPrimeProduct);

   PrintFile(LOGFILE, Sprintf("The largest squarefree eligible number is %o.", eligFromPrimes[1]));

   ternPrec := GetTernaryPrecision(eligFromPrimes[1], d, 6);
   maxPrec := ternPrec;
   PrintFile(LOGFILE, Sprintf("Computing the theta series for the ternary form up to precision %o.", ternPrec));

   splitTheta := BooleanTheta(S, ternPrec);
   excepts := checkEligibility(M, d, S, eligFromPrimes, splitTheta, ternPrec);
   unreps := [x : x in excepts];
   while #excepts gt 0 do
      eligSquares := EligibleWithSquares(F4bound, NNNN, chi, excepts, eligPrimes, aniso);
      if #eligSquares eq 0 then
         break;
      end if;

      ternPrec := GetTernaryPrecision(eligSquares[1], d, 6);
      if ternPrec gt maxPrec then
         maxPrec := ternPrec;
         splitTheta := BooleanTheta(S, ternPrec);
         PrintFile(LOGFILE, Sprintf("Recomputing ternary theta up to precision %o.", ternPrec));
      end if;

      excepts := checkEligibility(M, d, S, eligSquares, splitTheta, ternPrec);
      for x in excepts do
         Append(~unreps,x);
      end for;
   end while;


   tim2 := Cputime(tim);
   PrintFile(LOGFILE, Sprintf("The following numbers fail to be represented by the form: %o", unreps));
   PrintFile(LOGFILE, Sprintf("Time needed is %o sec.", tim2));
   return unreps;
end function;
