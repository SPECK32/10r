// MILP code to find a related key differential trail for 10 rounds SPECK32/64 based on the Table 8.
#include <fstream>
#include <iostream>
#include <math.h>
#include <bitset>
#include "gurobi_c++.h" // Gurobi Library
using namespace std;
#define BLOCK_SIZE (16) // it must be fix for SPECK32/64
#define ROUNDS (10) // >= 3. The number of rounds. This model works for 10 rounds of SPECK32/64.
#define RO (3) // It can be 2 to ROUNDS - 3. Based on Table 8, it is fixedto be 3.
int  W0, W1;
void define_data(GRBEnv env)
{
	W0 = 7;
	W1 = 2;
}
////////////////////////////////////////////////////////////////////////////////////////////
//                                 FUNCTIONS                                              //
///////////////////////////////////////////////////////////////////////////////////////////
/*This function helps us to apply our search strategy based on Fig.2.
In fact, the maximum number of the consecutive rounds of subkeys that
can have zero differential is 3 rounds.These 3 consecutive rounds of 
subkeys lead to four consecutive rounds with zero input differential
in the data path of SPECK.*/
static void Zero_Diff_Consecutive_Rounds(GRBEnv env, GRBModel& model, GRBVar N[][BLOCK_SIZE], GRBVar R2[][BLOCK_SIZE],GRBVar K[][BLOCK_SIZE])
{
	for (int i = 0; i < BLOCK_SIZE; i++)
	{
//	We set 4 consecutive rounds of data path to 0. 
		model.addConstr(N[RO - 1][i] == 0);
		model.addConstr(R2[RO - 1][i] == 0);
		model.addConstr(N[RO][i] == 0);
		model.addConstr(R2[RO][i] == 0);
		model.addConstr(N[RO + 1][i] == 0);
		model.addConstr(R2[RO + 1][i] == 0);
		model.addConstr(N[RO + 2][i] == 0);
		model.addConstr(R2[RO + 2][i] == 0);
//	We set 3 consecutive rounds of subkeys to 0. 
		model.addConstr(K[RO][i] == 0);
		model.addConstr(K[RO + 1][i] == 0);
		model.addConstr(K[RO + 2][i] == 0);
	}
}
// This function models the differential behavior of modular addition.
static void  Modular_Addition_Diff(GRBEnv env, GRBModel& model, int r,
	GRBVar A[][BLOCK_SIZE], GRBVar B[][BLOCK_SIZE], int b, GRBVar C[][BLOCK_SIZE], GRBVar Eqq[][BLOCK_SIZE - 1])
{
		for (int i = 1; i <= BLOCK_SIZE - 1; i++) {
			model.addConstr(A[r - 1][i] + B[b - 1][i] + C[r - 1][i] + Eqq[r - 1][i - 1] <= 3);
			model.addConstr(A[r - 1][i] + B[b - 1][i] + C[r - 1][i] - Eqq[r - 1][i - 1] >= 0);
			model.addConstr(A[r - 1][i] - B[b - 1][i] + Eqq[r - 1][i - 1] >= 0);
			model.addConstr(B[b - 1][i] - C[r - 1][i] + Eqq[r - 1][i - 1] >= 0);
			model.addConstr(-A[r - 1][i] + C[r - 1][i] + Eqq[r - 1][i - 1] >= 0);
		}
		GRBVar d[BLOCK_SIZE - 1];
		GRBVar f[BLOCK_SIZE - 1];
		for (int j = 0; j <= BLOCK_SIZE - 2; j++) {
			d[j] = model.addVar(0.0, 2.0, 0.0, GRB_INTEGER);
			f[j] = model.addVar(0.0, 1.0, 0.0, GRB_INTEGER);
		}
		model.update();
		for (int i = 0; i <= BLOCK_SIZE - 2; i++) {

			model.addConstr(A[r - 1][i] + B[b - 1][i] + C[r - 1][i] + C[r - 1][i + 1] - 2 * d[i] == f[i]);
			model.addConstr(f[i] <= Eqq[r - 1][i]);
		}
}
// MILP modeling for Xor function based on the Eq. (1).
static void XORR(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], GRBVar B[][BLOCK_SIZE], GRBVar C[][BLOCK_SIZE])
{
	for (int j = 0; j<BLOCK_SIZE; j++)
	{
		model.addConstr(A[num_rounds - 1][j] + B[num_rounds - 1][j] - C[num_rounds - 1][j] >= 0);
		model.addConstr(A[num_rounds - 1][j] - B[num_rounds - 1][j] + C[num_rounds - 1][j] >= 0);
		model.addConstr(-A[num_rounds - 1][j] + B[num_rounds - 1][j] + C[num_rounds - 1][j] >= 0);
		model.addConstr(-A[num_rounds - 1][j] - B[num_rounds - 1][j] - C[num_rounds - 1][j] >= -2);
	}
}
// MILP modeling for Xor function based on the Eq. (1).
static void XORRKEY(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], GRBVar B[][BLOCK_SIZE], int b, GRBVar C[][BLOCK_SIZE])
{
	for (int j = 0; j<BLOCK_SIZE; j++)
	{
		model.addConstr(A[num_rounds - 1][j] + B[b - 1][j] - C[num_rounds - 1][j] >= 0);
		model.addConstr(A[num_rounds - 1][j] - B[b - 1][j] + C[num_rounds - 1][j] >= 0);
		model.addConstr(-A[num_rounds - 1][j] + B[b - 1][j] + C[num_rounds - 1][j] >= 0);
		model.addConstr(-A[num_rounds - 1][j] - B[b - 1][j] - C[num_rounds - 1][j] >= -2);
	}

}
// MILP modeling for Xor function based on the Eq. (1).
static void XORRmod(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], GRBVar B[][BLOCK_SIZE], int b, GRBVar C[][BLOCK_SIZE])
{
	model.addConstr(A[num_rounds - 1][BLOCK_SIZE - 1] + B[b - 1][BLOCK_SIZE - 1] - C[num_rounds - 1][BLOCK_SIZE - 1] >= 0);
	model.addConstr(A[num_rounds - 1][BLOCK_SIZE - 1] - B[b - 1][BLOCK_SIZE - 1] + C[num_rounds - 1][BLOCK_SIZE - 1] >= 0);
	model.addConstr(-A[num_rounds - 1][BLOCK_SIZE - 1] + B[b - 1][BLOCK_SIZE - 1] + C[num_rounds - 1][BLOCK_SIZE - 1] >= 0);
	model.addConstr(-A[num_rounds - 1][BLOCK_SIZE - 1] - B[b - 1][BLOCK_SIZE - 1] - C[num_rounds - 1][BLOCK_SIZE - 1] >= -2);
}
// MILP modeling for w bits Leftshift.
static void LEFTSHIFT(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], int a, int w, GRBVar B[][BLOCK_SIZE])
{
	for (int j = 0; j<BLOCK_SIZE; j++)
		model.addConstr(B[num_rounds - 1][j] == A[a - 1][(j + w) % BLOCK_SIZE]);
}
// MILP modeling for w bits Righttshift.
static void
RIGHTSHIFT(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], int a, int w, GRBVar B[][BLOCK_SIZE])
{
	for (int j = 0; j<BLOCK_SIZE; j++)
		model.addConstr(B[num_rounds - 1][j] == A[a - 1][((j + (BLOCK_SIZE - w)) % (BLOCK_SIZE))]);
}
//##################################################################################################
int main(int argc, char *argv[])
{
	GRBEnv *env = 0;
	GRBVar *vars = 0;
	ofstream outputFile("output.dat", ios::out);
	if (!outputFile)
	{
		cerr << "some thing wrong during opening file!" << endl;
		exit(1);
	}

	try
	{
		GRBEnv env = GRBEnv();
		GRBModel model = GRBModel(env);
		define_data(env);

		// Set variables
		GRBVar L1[ROUNDS][BLOCK_SIZE];
		GRBVar L2[ROUNDS][BLOCK_SIZE];
		GRBVar R1[ROUNDS][BLOCK_SIZE];
		GRBVar R2[ROUNDS][BLOCK_SIZE];
		GRBVar N[ROUNDS][BLOCK_SIZE];
		GRBVar K[ROUNDS][BLOCK_SIZE];
		GRBVar LL[3][BLOCK_SIZE];
		GRBVar LL1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar O[ROUNDS - 1][BLOCK_SIZE];
		GRBVar RR1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar Eqq[ROUNDS][BLOCK_SIZE - 1];
		GRBVar Eqq_KEY[ROUNDS - 1][BLOCK_SIZE - 1];
		for (int i = 1; i<ROUNDS; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
				L1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
		for (int i = 0; i<ROUNDS; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
			{
				L2[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				R1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				R2[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				N[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				K[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}
		for (int i = 0; i<ROUNDS - 1; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
			{
				LL1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				O[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				RR1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}
		for (int i = 1; i<ROUNDS; i++)
			for (int j = 0; j<BLOCK_SIZE - 1; j++) {
				Eqq[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}
		for (int j = 0; j<BLOCK_SIZE - 1; j++)
			Eqq[0][j] = model.addVar(0.0, 0.0, 0.0, GRB_BINARY);
		for (int i = 0; i<ROUNDS - 1; i++)
			for (int j = 0; j<BLOCK_SIZE - 1; j++) {
				Eqq_KEY[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}
		for (int i = 0; i <= 2; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
				LL[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
		model.update();
		// Building MILP model for SPECK cipher
		// round 1
		XORR(env, model, 1, L2, K, N);
		XORR(env, model, 1, R1, N, R2);
		if (ROUNDS != 1)
			for (int i = 2; i <= ROUNDS; i++)
			{
				RIGHTSHIFT(env, model, i, N, i - 1, W0, L1);
				Modular_Addition_Diff(env, model, i, L1, R2, i - 1, L2, Eqq);
				XORR(env, model, i, L2, K, N);
				XORR(env, model, i, R1, N, R2);
				LEFTSHIFT(env, model, i, R2, i - 1, W1, R1);
				// for ARX
				XORRmod(env, model, i, L1, R2, i - 1, L2);
			}
		// Building MILP model for key schedule algorithm of SPECK
		for (int i = 1; i < ROUNDS; i++) 
		{
			if (i <= 3) {
				RIGHTSHIFT(env, model, i, LL, i, W0, LL1);
			}
			else if (i >= 4) {
				RIGHTSHIFT(env, model, i, O, i - 3, W0, LL1);
			}
			Modular_Addition_Diff(env, model, i, LL1, K, i, O, Eqq_KEY);
			LEFTSHIFT(env, model, i, K, i, W1, RR1);
			XORRKEY(env, model, i, RR1, K, i + 1, O);
			// for ARX
			XORRmod(env, model, i, LL1, K, i, O);
		}
		Zero_Diff_Consecutive_Rounds(env, model, N, R2, K);

		// Objective Function
		GRBLinExpr OBJfun, OBJfun_dATA, OBJfun_kEY, Calculate_Eqq[ROUNDS], Calculate_Eqq_Key[ROUNDS];
		model.update();
		for (int i = 1; i<ROUNDS; i++)
			for (int j = 0; j < BLOCK_SIZE - 1; j++) {
				OBJfun_dATA += (Eqq[i][j]);
				Calculate_Eqq[i] += (Eqq[i][j]);
			}
		for (int i = 0; i<ROUNDS - 1; i++)
			for (int j = 0; j < BLOCK_SIZE - 1; j++) {
				OBJfun_kEY += (Eqq_KEY[i][j]);
				Calculate_Eqq_Key[i] += (Eqq_KEY[i][j]);
			}
			OBJfun += (OBJfun_dATA + OBJfun_kEY);
			model.addConstr(OBJfun >= 1);

		model.update();
		model.setObjective(OBJfun, GRB_MINIMIZE);
		model.optimize();
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//										   Print the diff. trail for data path 			 	  		     	//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
			outputFile << "L2:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (L2[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "R1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (R1[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "N:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (N[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\t";
			outputFile << "R2:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (R2[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			if (ROUNDS != 1) {
				for (int i = 1; i<ROUNDS; i++)
				{
					outputFile << "\n---------------------------------------------------------------------------\n";
					outputFile << "Sequences of round: " << i + 1 << "\n" << endl;
					outputFile << "L:   ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (N[i - 1][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\t";
					outputFile << "R:   ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (R2[i - 1][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "L1:  ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (L1[i][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "R:   ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (R2[i - 1][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "L2:  ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (L2[i][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "R1:  ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (R1[i][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "N:  ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (N[i][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\t";
					outputFile << "R2:  ";
					for (int j = 0; j<BLOCK_SIZE; j++)
						outputFile << (R2[i][j].get(GRB_DoubleAttr_Xn));
					outputFile << "\n";
					outputFile << "The Probability is:\t" << Calculate_Eqq[i].getValue() << "\n";
				}
			}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//										Print the diff. trail for Key path	  						     	//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

		for (int i = 0; i<3; i++)
		{
			outputFile << "\n---------------------------------------------------------------------------\n";
			outputFile << "Sequences of round: " << i + 1 << "\n" << endl;
			outputFile << "LL:   ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (LL[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\t";
			outputFile << "K:   ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "LL1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (LL1[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "K:   ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			outputFile << "O:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (O[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			outputFile << "RR1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (RR1[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "O:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (O[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\t";
			outputFile << "K1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i + 1][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			outputFile << "The Probability is:\t" << Calculate_Eqq_Key[i].getValue() << "\n";
		}
		for (int i = 3; i<ROUNDS - 1; i++)
		{
			outputFile << "\n---------------------------------------------------------------------------\n";
			outputFile << "Sequences of round: " << i + 1 << "\n" << endl;
			outputFile << "O:   ";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (O[i - 3][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\t";
			outputFile << "K:   ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "LL1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (LL1[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "K:   ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "O:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (O[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "RR1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (RR1[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			outputFile << "O:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (O[i][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\t";
			outputFile << "K1:  ";
			for (int j = 0; j<BLOCK_SIZE; j++)
				outputFile << (K[i + 1][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			outputFile << "The Probability is:\t" << Calculate_Eqq_Key[i].getValue() << "\n";
		}

		outputFile << "\n\n\n";
		outputFile <<"Obj_KEY:\t"<< OBJfun_kEY.getValue()<<"\n";
		outputFile << "Obj_Data:\t" << OBJfun_dATA.getValue() << "\n";
		outputFile << "Obj:\t" << OBJfun.getValue() << "\n";

	}
	catch (GRBException e)
	{
		std::cout << "Error code = "
			<< e.getErrorCode()
			<< std::endl;
		std::cout << e.getMessage() << std::endl;
	}
	catch (...)
	{
		std::cout << "Exception during optimization"
			<< std::endl;
	}

	return 0;
}