#ifndef Minisat_PrintFlags_h
#define Minisat_PrintFlags_h

#define printFinalSolution
/* #define printFailLiteralDetectionData */
// #define printElimVarsData
/* #define printVivificationData */
/* #define printReduceDBdata */
/* #define printBackWardSubsumeData */
#define printIncompatibilities
// #define printLookahead

/*#define LAM_PRINT(thres, format...) \
do{ \
    if(thres >= 0) printf("" format);  \
}while(0)*/

#define LAM_PRINT(thres, format...) \
do { \
} while (0)

#endif
