//
//  HMCS_fairness_simulation.cpp
//
//
//  Created by Milind Chabbi on 8/19/14.
//
//
#include<vector>
#include<iostream>
#include<math.h>
#include<assert.h>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */

using namespace std;

#define UF1() ((ceil(n1 * 1.0 / k1) * k1 -n1) * (n2 * n3 -1))
#define UF2() ((ceil(n1 * n2 * 1.0 / k2) * k2 - n1 * n2) * (n3 -1))
#define UF3N1N2GTT1T2() ((ceil( n1 * n2 * 1.0 / (t1 * t2)) * t1 * t2 - n1 * n2) * (n3 -1) + (n2 -1) * ( ceil (n1 * 1.0 / t1) * t1 - n1) )

#define UF3N1N2LTT1T2() ( \
(ceil(n1 * 1.0 / t1 ) * ceil( n2 * 1.0 / t2 ) * t1 * t2 - n1 * n2) * (n3 -1) + \
(n2 -1) * ( ceil (n1 * 1.0 / t1) * t1 - n1) )


#define UF3CEILCEIL() ((ceil(ceil(n1 * 1.0 / t1 ) * n2 * 1.0 / t2 ) * t1 * t2 - n1 * n2) * (n3 -1) + (n2 -1) * ( ceil (n1 * 1.0 / t1) * t1 - n1) )


#define MAX_ITER (n1 * n2 * n3)




//int t1 = 4;
//int t2 = 8;
//int k1 = 3;
//int k2 = 5;



struct QNode{
    long oldMax;
    long oldServiceNo;
    vector<QNode> childQ;
    long resumeAt;
    
    QNode(): oldServiceNo(0), oldMax(0), resumeAt(0) {
    }
};



int main(){
    
    int n1 = 4;
    int n2 = 8;
    int n3 = 2;
    long gServiceNo;
    
    // Inner cohort
    vector<QNode> innerCohort;
    for (int i = 0; i < n2 * n3; i++) {
        QNode q1;
        for (int j = 0; j < n1; j++) {
            QNode q2;
            q1.childQ.push_back(q2);
        }
        innerCohort.push_back(q1);
    }
    
    for(int k1 = 1; k1 < 0; k1 ++) {
        
        // Reset
        for (int i = 0; i < n2 * n3; i++) {
            for (int j = 0; j < n1; j++) {
                innerCohort[i].childQ[j].resumeAt = 0;
                innerCohort[i].childQ[j].oldMax = 0;
                innerCohort[i].childQ[j].oldServiceNo = 0;
            }
        }
        
        gServiceNo = 0;
        // Simulate Inner cohort
        for (int i = 0; i < MAX_ITER; i++) {
            QNode * node =  &innerCohort[i % (n2 * n3)];
            const long startPoint = node->resumeAt;
            for (long j = startPoint; j < startPoint + k1; j++) {
                int index = j % n1;
                node->childQ[index].oldMax = max(node->childQ[index].oldMax, gServiceNo - node->childQ[index].oldServiceNo - n1 * n2 * n3);
                node->childQ[index].oldServiceNo = gServiceNo++;
                
            }
            node->resumeAt = (startPoint + k1) % n1;
        }
        
        long observedUF1 = 0;
        for (int i = 0; i < n2 * n3; i++) {
            QNode * node = &innerCohort[i];
            for (int j = 0; j < n1; j++) {
                observedUF1 = max(observedUF1 , node->childQ[j].oldMax);
            }
        }
        
        long expectedUF1 = UF1();
        cout<<"Expected UF1 = " << expectedUF1 << endl;
        cout<<"Observed UF1 = " << observedUF1 << endl;
        assert(expectedUF1 == (long)observedUF1);
    }
    
    
    
    //  Outer cohort
    vector<QNode> outerCohort;
    for (int i = 0; i < n3; i++) {
        QNode q1;
        for (int j = 0; j < n1 * n2; j++) {
            QNode q2;
            q1.childQ.push_back(q2);
        }
        outerCohort.push_back(q1);
    }
    
    for(int k2 = 2; k2 < 0; k2 ++) {
        
        //  Reset
        vector<QNode> outerCohort;
        for (int i = 0; i < n3; i++) {
            for (int j = 0; j < n1 * n2; j++) {
                outerCohort[i].childQ[j].resumeAt = 0;
                outerCohort[i].childQ[j].oldMax = 0;
                outerCohort[i].childQ[j].oldServiceNo = 0;
            }
        }
        
        gServiceNo = 0;
        // Simulate Outer cohort
        for (int i = 0; i < MAX_ITER; i++) {
            QNode * node =  &outerCohort[i % n3];
            const long startPoint = node->resumeAt;
            for (long j = startPoint; j < startPoint + k2; j++) {
                int index = j % (n1* n2);
                node->childQ[index].oldMax = max(node->childQ[index].oldMax, gServiceNo - node->childQ[index].oldServiceNo - n1 * n2 * n3);
                node->childQ[index].oldServiceNo = gServiceNo++;
                
            }
            node->resumeAt = (startPoint + k2) % (n1 * n2);
        }
        
        long observedUF2 = 0;
        for (int i = 0; i < n3; i++) {
            QNode * node = &outerCohort[i];
            for (int j = 0; j < n1 * n2; j++) {
                observedUF2 = max(observedUF2 , node->childQ[j].oldMax);
            }
        }
        
        long expectedUF2 = UF2();
        cout<<"Expected UF2 = " << expectedUF2 << endl;
        cout<<"Observed UF2 = " << observedUF2 << endl;
        assert(expectedUF2 == (long) observedUF2);
    }
    
    
    // 3-level
    
    srand (time(NULL));
    
    while (1) {
        
        // test t1 < n1
        n1 = max(2, rand() % 20);
        n2 = max(2, rand() % 10);
        //n3 = max(2, rand() % 20);
        n3 = 2;
        int t1 = max(1, rand() % 1000);
        int t2 = max(1, rand() % 1000);
        
        //n1 = 10, n2 = 8, n3 = 2, t1 = 7, t2 = 476;
        
        
        //        for(int t1 = n1; t1 < 100; t1 ++) {
        //            for(int t2 = 2; t2 < 100; t2 ++) {
        {{
            
            // 3level
            vector<QNode> hmcs;
            for (int i = 0; i < n3; i++) {
                QNode q1;
                for (int j = 0; j < n2; j++) {
                    QNode q2;
                    for (int k = 0; k < n1; k++) {
                        QNode q3;
                        q2.childQ.push_back(q3);
                    }
                    q1.childQ.push_back(q2);
                }
                hmcs.push_back(q1);
            }
            
            
            gServiceNo = 0;
            // Simulate 3-level
            for (int i = 0; i < MAX_ITER; i++) {
                QNode * node1 =  &hmcs[i % n3];
                const long startPoint1 = node1->resumeAt;
                for (long j = startPoint1; j < startPoint1 + t2; j++) {
                    QNode * node2 =  & (node1->childQ[j % n2]);
                    const long startPoint2 = node2->resumeAt;
                    for (long k = startPoint2; k < startPoint2 + t1; k++) {
                        const int index = k % n1;
                        node2->childQ[index].oldMax = max(node2->childQ[index].oldMax, gServiceNo - node2->childQ[index].oldServiceNo - n1 * n2 * n3);
                        node2->childQ[index].oldServiceNo = gServiceNo++;
                    }
                    node2->resumeAt = (startPoint2 + t1) % n1;
                }
                node1->resumeAt = (startPoint1 + t2) % n2;
            }
            
            long observedUF3 = 0;
            for (int i = 0; i < n3; i++) {
                QNode * node1 = &hmcs[i];
                for (int j = 0; j < n2; j++) {
                    QNode * node2 = &(node1->childQ[j]);
                    for (int k = 0; k < n1; k++) {
                        observedUF3 = max(observedUF3 , node2->childQ[k].oldMax);
                    }
                }
            }
            
            long expectedUF3 = UF3CEILCEIL(); // n1 * n2 < t1 * t2 ?  UF3N1N2GTT1T2(): UF3N1N2LTT1T2() ;
            
            //cout<<"Expected UF3N1N2GTT1T2 = " << UF3CEILCEIL() << endl;
            //cout<<"Expected UF3N1N2LTT1T2 = " << UF3N1N2LTT1T2() << endl;
            
            cout<<"Expected UF3 = " << expectedUF3 << endl;
            cout<<"Observed UF3 = " << observedUF3 << endl;
            assert(UF3CEILCEIL() == observedUF3 || UF3N1N2LTT1T2() == observedUF3);
            //assert(expectedUF3 == observedUF3);
        }
        }
    }
    
}
