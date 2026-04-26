#!/usr/bin/env python3
"""
Coh Simulation Visualization - ASCII art version
"""

def print_coh_flow():
    print("""
+====================================================================+
|              COH CATEGORICAL COMPUTATION FRAMEWORK                  |
|                  COMPUTATION FLOW                               |
+====================================================================+

    +-----------------------+        +-----------------------+            
    |    HIDDEN LAYER      |        |   OBSERVABLE LAYER   |            
    |  (Internal Compute)  |        |  (External Behavior) |            
    +-----------------------+        +-----------------------+            
    |  x = [a,1.0][b,1.5]  |=====>  |  R = [a][b]         |            
    |  cost = 2.5          | proj  |  cost = 2.0          |            
    +-----------------------+        +-----------------------+            
              |                           |                       
              | compose                  |                       
              V                                                   
    +-----------------------------------------------+            
    |           d = sup(hidden costs over fiber)   |            
    |           d(R) = sSup{cost(x) | proj(x) = R}  |            
    |           d = 3.0  (hidden can exceed)         |            
    +-----------------------------------------------+            
                        |                                       
                        V                                       
    +-----------------------------------------------+            
    |          COH FUNDAMENTAL INEQUALITY          |            
    |                                              |            
    |   V(y) + spend  <=  V(x) + d                |            
    |   3.0  + 2.0   <=  5.0  + 3.0                |            
    |      5.0        <=      8.0   VERIFIED       |            
    +-----------------------------------------------+            
""")

def print_composition():
    print("""
+====================================================================+
|                    COMPOSITION & SUBADDITIVITY                      |
+====================================================================+

    f: x--[a]-->y                    g: y--[b]-->z               
    |       obs: a                   |       obs: b               
    |       spend: 2.0               |       spend: 1.5              
    V                           V                                  
    R1=[a], d1=2.0              R2=[b], d2=1.5                     
    |                           |                               
    |          COMPOSE           |                               
    +---------------------------+                               
                        |                                       
                        V                                       
              +-----------------------+                           
              |  h: x--[a][b]-->z   |                           
              |  R12 = [a,b]        |                           
              |  spend = 3.5        |                           
              |  d12 = 3.5          |                           
              +-----------------------+                           

    SUBADDITIVITY: d(R1++R2) <= d(R1) + d(R2)                      
    VERIFICATION: 3.5 <= 2.0 + 1.5 = 3.5 VERIFIED                  
""")

def print_fiber():
    print("""
+====================================================================+
|                         FIBER & DECOMPOSITION                     |
+====================================================================+

    OBSERVABLE: R = [a, b]          (cost: 2.0)                   

    +-----------------------------------------------+              
    |                    FIBER(R)                   |              
    |     { x in Hidden | proj(x) = R }            |              
    +-----------------------------------------------+              
                         |                                          
         +----------------+-------------------+                        
         V                V                                          
    +---------+      +---------+                                      
    | x1:[a][b]  |    | x2:[a,X]  |                             
    | cost: 2.0 |    | cost: 3.0 |  <-- hidden can exceed       
    +---------+      +---------+                                      
         min               sup = d                                  

    d(R) = sup{cost(x)} = 3.0                                     

    DECOMPOSITION: R can be split into R1, R2                      
    x = x1 ++ x2  where  proj(x1) = R1, proj(x2) = R2          
""")

def main():
    print("\n" + "="*70)
    print("         COH CATEGORICAL COMPUTATION - ASCII VISUALIZATION")
    print("="*70 + "\n")
    
    print_coh_flow()
    print()
    print_composition()
    print()
    print_fiber()
    
    print("""
+====================================================================+
|                          SUMMARY                                 |
+====================================================================+

  KEY CONCEPTS:
  * Hidden Layer: Exact computation with costs                       
  * Observable: External behavior visible to adversary               
  * Projection: Maps hidden --> observable                          
  * Delta (d): Supremum of hidden costs over fiber                    
  * Inequality: V(y) + spend <= V(x) + d                       

  PROPERTIES:
  * d(id) = 0 (identity has zero defect)                        
  * d(R1++R2) <= d(R1) + d(R2) (subadditivity)              
  * d(R) > 0 if hidden can exceed (structural independence)       
""")

if __name__ == "__main__":
    main()