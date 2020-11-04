# 27-01-2019

## Question 1

**Which of the following Hoare triples is FALSE?**

**a.** {k > 0} while i > k do i := i - k {i < k}  
**b.** {true} if x > 0 then y := x else y := -x {y  ≥ 0}  
**c.** {x = 1} skip {x ≥ 0}  
**d.** {x = 1} x := x - 1 {x ≥ 0}  

**Answer:** A  

## Question 2

**Which of the following Hoare triples is FALSE?**
[Hint: In case of doubt, calculate the weakest precondition.]

**a.** {x > 0} x := z - x; y := z - x {y > 0}  
**b.** {x ≥ 0} x :=  x + y; y := x - y {y > 0}  
**c.** {x < y} x := z - x; y := z - y {x > y}  
**d.** {x > 0} z := 1; y := x + z {y > 0}  

**Answer:** B   


## Question 3

**Which of the following expressions gives or is equivalent to the weakest precondition of the following Hoare triple?**
   ```
   {wp} if  x > y then z := x else z := y {z < x}
   ```

**a.** x > y    
**b.** y > x     
**c.** false     
**d.** true      

**Answer:** C  
**Justification:**
```
wp((if  x > y then z := x else z := y), z < x)
= x > y ∧ x < x ∨ x <= y ∧ y < x
= false ∨  false
= false
``` 

