/* Eligible Numbers functions */

// Gets the index in the bit array for the boolean theta for which to place the boolean
// We have to add 1 to stuff because magma's 1 based indexing is annoying
function GetIndex(index, modulus)
   whichint := (index div modulus) + 1;
   whichbit := (index mod modulus);
   orint := 1;
   orint := ShiftLeft(1, whichbit);

   return whichint, orint;
end function;

// Reads from the boolean theta whether the number is represented 
function bitread(seq, index, modulus)
   whichint, orint := GetIndex(IntegerRing()!index, modulus);

   if BitwiseAnd(seq[whichint],orint) ne 0 then
      return true;
   end if;

   return false;
end function;

// Computes B(p) naively given a solitary prime
function BoundPrimeNaive(p, power, level, chi)
   specialProduct := chi(p) eq -1 and not IsDivisibleBy(level,p) select (p - 1) / (p + 1) else 1;
   return (Sqrt(p^power) / (power + 1)) * specialProduct;
end function;

// A better (faster) way to compute B(m) by taking the product of B(p) for each prime in the prime factorization of m.
// This is faster since we store the already computed values of B(p) for each prime.
// Note: we don't actually pass the number m; rather, we pass the sequence of primes, since this is quicker than factoring.
// Note/Warning: Only works on squarefree numbers. Otherwise, use BoundM!
function BetterBound(primes)
   assert #primes gt 0;
   return &*[prime[2] : prime in primes];
end function;

// Computes the bound on an arbitrary m (requires factoring---slow, would not recommend using unless necessary).
function BoundM(m, level, chi, aniso)
   if m eq 1 then
      return 1;
   else
      arr := [BoundPrimeNaive(p[1],p[2],level,chi) : p in Factorization(m) | not p[1] in aniso];
      if #arr gt 0 then
         return &*arr;
      else
         anisoFactors := [p : p in Factorization(m) | p[1] in aniso];
         specialProd := &*[chi(p[1]) eq -1 and not IsDivisibleBy(level, p[1]) select (p[1]-1) / (p[1]+1) else 1 : p in anisoFactors];
         return 1/&*[p[2] + 1 : p in anisoFactors]*specialProd;
      end if;
   end if;
end function;

// Returns a list of B(p)'s where B(p) < 1. We only need to check 2,3,5,7 because
// for primes >= 11, B(p) is guaranteed at least 1
function GetBpLt1(level,chi)
   return [bp : p in [2,3,5,7] | bp lt 1 where bp is BoundPrimeNaive(p,1,level,chi)];
end function;

// Get the bound on B(p) for elig primes, i.e. every eligible prime p must have
// B(p) lt return value
function GetEligPrimesBound(bound, level, chi)
   return bound / (&*GetBpLt1(level,chi));
end function;

// Gets all eligible primes, sorted by B(p)
function GetEligiblePrimes(upperBound, level, chi)
   eligiblePrimes := [];

   // Computes the sequence of eligible primes, stored as tuples of the prime p and B(p).
   p := NextPrime(1);
   boundP := BoundPrimeNaive(p,1,level,chi);

   // This inequality could be strict, but we're playing it safe
   while boundP le upperBound do
      Append(~eligiblePrimes,<p,boundP>);
      p := NextPrime(p);
      boundP := BoundPrimeNaive(p,1,level,chi);
   end while;

   for i in [1..10] do
      if boundP le upperBound then
         Append(~eligiblePrimes, <p, boundP>);
      end if;
      p := NextPrime(p);
      boundP := BoundPrimeNaive(p,1,level,chi);
   end for;

   return Sort(eligiblePrimes, func<p1,p2 | p1[2] - p2[2]>);
end function;

// Computes the eligible numbers, following the algorithm from the 290 preprint.
// Heavily inspired by Hanke's C++ code to do the same thing =)
function EligibleNumbers(r, eligiblePrimes, bound)
   eligNums := [];
   primesIndices := [1..r];
   curIdx := r;
   done := false;

   while not done do
      carry := false;
      if primesIndices[r] le #eligiblePrimes then
         rPrimes := [eligiblePrimes[i] : i in primesIndices];
         boundM := BetterBound(rPrimes);

         // Note how this is less than or equal, rather than just less than.
         // Theoretically, we only need less than, but we include equal just to be safe (after all, we would just have a few more eligible numbers).
         if boundM le bound then
            Append(~eligNums,&*[prime[1] : prime in rPrimes]);
            primesIndices[r] := primesIndices[r] + 1;
            curIdx := r;
         else
            carry := true;
         end if;
      else
         carry := true;
      end if;

      if carry then
         if curIdx gt 1 then
            curIdx := curIdx - 1;
            primesIndices[curIdx] := primesIndices[curIdx] + 1;
            for i in [curIdx+1..r] do
               primesIndices[i] := primesIndices[curIdx] + i - curIdx;
            end for;
         else
            done := true;
         end if;
      end if;
   end while;

   return eligNums;
end function;

// Computes eligible numbers of the form ourNumber*p^2.
// Note: when passing in our number, it should be a tuple of <ourNumber, B(ourNumber)>.
function PrimesSquares(eligiblePrimes, bound, ourNumber,level,chi, aniso)
   eligSquares := [];
   i := 1;
   p := eligiblePrimes[i];

   // Note: again, theoretically this inequality could be strict, but we're playing it on the safe side.
   while BoundM(ourNumber*(p[1])^2, level, chi, aniso) le bound do
      Append(~eligSquares, ourNumber * (p[1])^2);
      i := i + 1;
      if i gt #eligiblePrimes then
         break;
      end if;
      p := eligiblePrimes[i];
   end while;

   return eligSquares;
end function;

// Gets the maximum number of primes we multiply before exceeding the bound for eligible numbers
function GetMaxNumPrimes(eligiblePrimes, bound)
   prodBound := 1;
   i := 0;
   while prodBound le bound do
      i := i + 1;
      if i gt #eligiblePrimes then
         break;
      end if;
      prodBound := prodBound * eligiblePrimes[i][2];
   end while;
   return i - 1;
end function;

// Can be used to compute the theta series for both the ternary and full form
// Precondition: must have prec > 0
function ComputeTheta(lattice, prec)
   assert prec gt 0;
   theta := ThetaSeries(lattice,prec);
   return theta;
end function;

// Gets sequence numbers up to precision which are not represented by the form
// theta is the sequence of coefficients for the theta series
// Generally, the theta series should be computed to a reasonably high precision, say, greater than 1000 (which is also probably overkill for our stuff)
function GetExceptions(theta, prec)
   return [n : n in [0..prec] | Coefficient(theta,n) eq 0];
end function;

// Returns sequence of sequences of eligible numbers taken as products of primes
function EligibleFromPrimes(bound, eligPrimes, maxNumPrimes)
   return Reverse(Sort(&cat[EligibleNumbers(i,eligPrimes,bound) : i in [1..maxNumPrimes]] cat [1]));
end function;

// Returns sequence of sequences of eligible numbers of the form m*p^2 for each excepted number m
function EligibleWithSquares(bound, level, chi, exceptions, eligPrimes,aniso)
   return Reverse(Sort(&cat[PrimesSquares(eligPrimes,bound,except,level,chi,aniso) : except in exceptions]));
end function;

// Takes the eligible numbers as products of distinct primes and eligible numbers as m*p^2 and flattens them into a reverse sorted sequence of all eligible numbers
// Also appends 1 to the list of eligible numbers, since this won't ever get generated as the
// product of primes (we don't consider product of zero primes).
function AllEligibleNumbers(eligFromPrimes,eligWithSquares)
   return Reverse(Sort(&cat(eligFromPrimes cat eligWithSquares) cat [1]));
end function;

// Gets the precision to which to calculate the theta series for the ternary subform.
// Should be of the form Ceiling(2 * d * Sqrt(maxNumber) * scale);
function GetTernaryPrecision(maxNumber,d, scale)
   return Ceiling(2 * d * Sqrt(maxNumber) * scale);
end function;


// Checks for representability of eligible numbers on the ternary subform T', where the full form is
// T = dx^2 + T'.
// More correctly, looks at representability of m - dx^2 in ternary form, and returns a list
// of those m who fail to be represented within the precision of the form.
function CheckEligibleOnTernary(eligNumbers, splitTheta, d, prec)
   notCovered := [];

   for num in eligNumbers do
      x := Floor(Sqrt(num / d));
      //while num - d * x^2 gt 0 and num - d * x^2 le prec and Coefficient(splitTheta,num - d * x^2) eq 0 do
      while num - d * x^2 gt 0 and num - d * x^2 le prec and bitread(splitTheta, num - d * x^2, 64) eq false do
         x := x - 1;
      end while;
      //if num - d * x^2 le 0 or num - d * x^2 gt prec or Coefficient(splitTheta,num - d * x^2) eq 0 then
      if num - d * x^2 le 0 or num - d * x^2 gt prec or bitread(splitTheta, num - d*x^2,64) eq false then
         Append(~notCovered, num);
      end if;
   end for;

   return notCovered;
end function;

// Checks for representability of eligible numbers on the full quadratic form.
// Usually these numbers are only those which fail to be represented by the ternary form up to precision
function CheckEligibleOnFull(eligNumbers,fullTheta)
   return [num : num in eligNumbers | Coefficient(fullTheta,num) eq 0];
end function;

// Boolean theta computation
// Almost identical to Hanke's/Jeremy's versions, but with slightly different bounds.
function BooleanTheta(ternMat, thetaPrec)
   //xySubformDisc := ternMat[1,1] * ternMat[2,2] -  ternMat[1,2] * ternMat[2,1];
   //ternaryDisc := ternMat[1,1] * ternMat[2,2] * ternMat[3,3] + ternMat[1,2] * ternMat[2,3] * ternMat[3,1] + ternMat[1,3] * ternMat[2,1] * ternMat[3,2] - ternMat[3,2] * ternMat[2,3] * ternMat[1,1] - ternMat[3,3] * ternMat[2,1] * ternMat[1,2];
   q11 := ternMat[1,1] / 2;
   q22 := ternMat[2,2] / 2;
   q33 := ternMat[3,3] / 2;
   q12 := ternMat[1,2];
   q13 := ternMat[1,3];
   q23 := ternMat[2,3];
   
   zDisc := 4 * q11 * q22 - q12 * q12;
   ternDisc := 4 * q11 * q22 * q33 - (q11 * q23 + q22 * q13 + q33 * q12) + q12 * q23 * q13;
   //thetaPrec2 := Ceiling(Sqrt(2 * thetaPrec + 1) * Sqrt(xySubformDisc / ternaryDisc));
   thetaPrec2 := Ceiling(Sqrt(thetaPrec * zDisc / ternDisc));
   printf "thetaPrec2=%o\n", thetaPrec2;
   thetaPrec3 := thetaPrec2 gt 800 select 800 else thetaPrec2;

   ternTheta := [0 : i in [0..(thetaPrec div 64) + 1]];
   whichint, orint := GetIndex(0, 64);
   ternTheta[whichint] := BitwiseOr(ternTheta[whichint], orint);

   for z in [thetaPrec2..0 by -1] do
      zTerm := q33 * z * z;
      for y,x in [-Ceiling(thetaPrec3/2)..Ceiling(thetaPrec3/2)] do
         yzTerm := zTerm + q22 * y * y + q23 * y * z;
         val := yzTerm + q11 * x * x + q12 * x * y + q13 * x * z;
         if val le thetaPrec and val gt 0 then
            whichint, orint := GetIndex(IntegerRing()!val, 64);
            ternTheta[whichint] := BitwiseOr(ternTheta[whichint], orint);
         end if;
      end for;
   end for;

   return ternTheta;
end function;

// Another boolean theta implementation, which uses Magma's built in ShortVectorsProcess command
// to generate vectors, rather than doing it manually.
// Not approximate, should not be called ``better''
function BetterBooleanTheta(lattice, prec)
   t := [0 : i in [0..(prec div 64) + 1]]; // +1 just to be safe

   whichint, orint := GetIndex(0, 64);
   t[whichint] := BitwiseOr(t[whichint], orint);

   P := ShortVectorsProcess(lattice,prec);
   while bitread(t, prec, 64) eq false  or not IsEmpty(P) do
      v, norm := NextVector(P);
      whichint, orint := GetIndex(IntegerRing()!norm, 64);
      t[whichint] := BitwiseOr(t[whichint], orint);
   end while;

   return t;
end function;
