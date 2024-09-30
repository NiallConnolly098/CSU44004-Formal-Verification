// Niall Connolly 20332921
// Jacob Wilson Sharpe

// Method 1 The following method should return true if and only if pre is a prefix of str. That is, str starts with pre.
method isPrefix(pre: string, str: string) returns (res:bool) 
  {
    if(|pre|==0){return true;}
    if(|str| < |pre|){return false;}
    return pre == str[..|pre|];
}

// Method 2 The following method should return true if and only if sub is a substring of str. That is, str contains sub.
method isSubstring(sub: string, str: string) returns (res:bool) {
  if(|sub|==0){return true;}
  var i:=0;
  while (i < |str|){
    var prefix:=isPrefix(sub, str[i..]); 
    if(prefix) {
      return true; 
    }
    else {
      i := i+1;
    }
  }
  return false;
}

// Method 3 The following method should return true if and only if str1 and str1 have a common substring of length k.
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool) {
  if(k==0){
    return true;
  }
  var i:=0;
  while(i < |str1|){
    if(|str1[i..]|<k) {return false;}
    var index:=i+k;
    var subFound:=isSubstring(str1[i..index],str2);
    if subFound {return true;}
    i:=i+1;
  }
  return false;
}

// Method 4 The following method should return the natural number len which is equal to the length of the longest 
//          common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat) {
  len := 0;
  var i := 1;
  while(i < |str1|){
    var subFound := haveCommonKSubstring(i, str1, str2);
    if subFound {len := i;}
    i := i+1;
  }
  return len;
}