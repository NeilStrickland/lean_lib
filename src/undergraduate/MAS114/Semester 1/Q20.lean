import tactic.norm_num

namespace MAS114
namespace exercises_1
namespace Q20

lemma L1 : nat.gcd 896 1200 = 16 := 
begin
 have e0 : 1200 % 896 = 304 := by norm_num,
 have e1 :  896 % 304 = 288 := by norm_num,
 have e2 :  304 % 288 =  16 := by norm_num,
 have e3 :  288 %  16 =   0 := by norm_num,
 exact calc
  nat.gcd 896 1200 = nat.gcd 304 896 : by rw[nat.gcd_rec,e0]
               ... = nat.gcd 288 304 : by rw[nat.gcd_rec,e1] 
               ... = nat.gcd  16 288 : by rw[nat.gcd_rec,e2] 
               ... = nat.gcd   0  16 : by rw[nat.gcd_rec,e3] 
               ... = 16 : rfl
end

lemma L2 : nat.gcd 123456789 987654321 = 9 := 
begin
 have e0 : 987654321 % 123456789 = 9 := by norm_num,
 have e1 : 123456789 % 9 = 0 := by norm_num,
 exact calc
  nat.gcd 123456789 987654321 
       = nat.gcd 9 123456789  : by rw[nat.gcd_rec,e0]
   ... = nat.gcd 0 9          : by rw[nat.gcd_rec,e1]
   ... = 9 : rfl
end

end Q20
end exercises_1
end MAS114