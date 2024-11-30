predicate isPrefixPred(pre:string, str:string)
{
  (|pre| <= |str|) &&
  pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
  (|pre| > |str|) ||
  pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
  ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
  ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
  ensures !res <==> isNotPrefixPred(pre,str)
  ensures  res <==> isPrefixPred(pre,str)
{
  return (|pre| == 0 || (|pre| <= |str| && pre == str[..|pre|]));
}
predicate isSubstringPred(sub:string, str:string)
{
  (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
  (forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
  ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
  ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
  ensures  res <==> isSubstringPred(sub, str)
  ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
  requires |sub| >= 0 && |str| >= 0
{
  var i:=0;
  while i <= |str| - |sub|
    invariant (forall j ::  0 <= j < i ==> 0 <= j + |sub| <= |str| && isNotPrefixPred(sub, str[j..]))
  {
    var prefix := isPrefix(sub, str[i..]);
    if (prefix) {
      return true;
    }
    i := i + 1;
  }
  return false;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
  ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
  ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

lemma haveCommon0SubstringLemma(str1:string, str2:string)
  ensures  haveCommonKSubstringPred(0,str1,str2)
{
  assert isPrefixPred(str1[0..0], str2[0..]);
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
  ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  if(|str1| < k) {return false;}
  found := false;
  var i:=0;
  while(i <= |str1| - k && !found)
    invariant |str1| >= k ==> 0 <= i <= |str1| - k + 1
    invariant !found <==> forall j, l :: (0 <= j < i && l == j + k ==> isNotSubstringPred(str1[j..l], str2))
  {
    var index := i+k;
    var subFound:=isSubstring(str1[i..index],str2);
    if (subFound) {found := true;}
    i:=i+1;
  }
  return found;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
  requires (|str1| <= |str2|)
  ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
  ensures haveCommonKSubstringPred(len,str1,str2)
{
  len := |str1|;
  while(len > 0)
    invariant forall k :: (len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2))
  {
    var subFound := haveCommonKSubstring(len, str1, str2);
    if (subFound) {return len;}
    len := len - 1;
  }
  assert isPrefixPred(str1[0..0], str2[0..]);
  return len;
}