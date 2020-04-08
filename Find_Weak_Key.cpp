// MILP code to find a weak key for 10 rounds SPECK32/64 in Table 8.
#include <fstream>
#include <iostream>
#include <math.h>
#include <bitset>
#include "gurobi_c++.h" // Gurobi Library

using namespace std;
#define BLOCK_SIZE (16) // it must be fix for SPECK32/64
#define ROUNDS (10) // >= 3 ; The number of rounds. The model works for 10 rounds of SPECK32/64.
int  W0, W1;
void define_data(GRBEnv env)
{
	W0 = 7;
	W1 = 2;
}

/*This function fixes the key differentials for all 10 rounds for SPECK32/64. 
The differentials are fixed based on the Table 8.*/
static void Rounds_Key_Diff(GRBEnv env, GRBModel& model, GRBVar K[][BLOCK_SIZE], GRBVar LL[][BLOCK_SIZE])
{
	GRBConstr l0[BLOCK_SIZE], l1[BLOCK_SIZE], l2[BLOCK_SIZE], k0[BLOCK_SIZE],
			  O1[BLOCK_SIZE], O2[BLOCK_SIZE], O3[BLOCK_SIZE], O4[BLOCK_SIZE],
			  O5[BLOCK_SIZE], O6[BLOCK_SIZE], O7[BLOCK_SIZE], O8[BLOCK_SIZE],
			  O9[BLOCK_SIZE], O10[BLOCK_SIZE];

	for (int i = 0; i < BLOCK_SIZE; i++)
	{
		l0[i] = model.addConstr(LL[0][i] == 0);
		l1[i] = model.addConstr(LL[1][i] == 0);
		l2[i] = model.addConstr(LL[2][i] == 0);
		k0[i] = model.addConstr(K[0][i] == 0);
		O1[i] = model.addConstr(K[1][i] == 0);
		O2[i] = model.addConstr(K[2][i] == 0);
		O3[i] = model.addConstr(K[3][i] == 0);
		O4[i] = model.addConstr(K[4][i] == 0);
		O5[i] = model.addConstr(K[5][i] == 0);
		O6[i] = model.addConstr(K[6][i] == 0);
		O7[i] = model.addConstr(K[7][i] == 0);
		O8[i] = model.addConstr(K[8][i] == 0);
		O9[i] = model.addConstr(K[9][i] == 0);
	}
	// Fixed key differentials based on Table 8.
	int Key1 = 0x0001;
	int ll0 = 0x0080;
	int ll1 = 0x0200;
	int ll2 = 0x2800;
	int Key2 = 0x0004;
	int Key3 = 0x0010;
	int Key4 = 0x0000;
	int Key5 = 0x0000;
	int Key6 = 0x0000;
	int Key7 = 0x8000;
	int Key8 = 0x8002;
	int Key9 = 0x8008;
	int Key10 = 0x812a;
	//  Add key differentials to the MMILP model
	int a = BLOCK_SIZE - 1;
	for (int j = 0; j < BLOCK_SIZE; j++)
	{
		l0[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(ll0)[a]);
		l1[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(ll1)[a]);
		l2[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(ll2)[a]);
		k0[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key1)[a]);
		O1[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key2)[a]);
		O2[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key3)[a]);
		O3[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key4)[a]);
		O4[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key5)[a]);
		O5[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key6)[a]);
		O6[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key7)[a]);
		O7[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key8)[a]);
		O8[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key9)[a]);
		O9[j].set(GRB_DoubleAttr_RHS, (int)bitset<16>(Key10)[a]);
		a--;
	}
}
// This function models the modular addition.
static void Modular_Addition(GRBEnv env, GRBModel& model, int r,
	GRBVar x[][BLOCK_SIZE], GRBVar y[][BLOCK_SIZE], GRBVar z[][BLOCK_SIZE], GRBVar c[][BLOCK_SIZE])
{
	model.addConstr(c[r - 1][BLOCK_SIZE - 1] == 0);
	for (int i = 1; i <= BLOCK_SIZE - 1; i++) {
		model.addConstr(x[r - 1][i] + y[r - 1][i] - c[r - 1][i - 1] >= 0);
		model.addConstr(x[r - 1][i] + c[r - 1][i] - c[r - 1][i - 1] >= 0);
		model.addConstr(y[r - 1][i] + c[r - 1][i] - c[r - 1][i - 1] >= 0);
		model.addConstr(-y[r - 1][i] - c[r - 1][i] + c[r - 1][i - 1] >= -1);
		model.addConstr(-x[r - 1][i] - c[r - 1][i] + c[r - 1][i - 1] >= -1);
		model.addConstr(-x[r - 1][i] - y[r - 1][i] + c[r - 1][i - 1] >= -1);
	}
	GRBVar d[BLOCK_SIZE];
		for (int j = 0; j<BLOCK_SIZE; j++)
			d[j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
		model.update();
	for (int i = 0; i <= BLOCK_SIZE - 1; i++) {
		model.addConstr(x[r - 1][i] + y[r - 1][i] + z[r - 1][i] + c[r - 1][i] - 2* d[i] == 0);
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
static void
LEFTSHIFT(GRBEnv env, GRBModel& model, int num_rounds, GRBVar A[][BLOCK_SIZE], int a, int w, GRBVar B[][BLOCK_SIZE])
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
	ofstream outputFile("Print_Key_values.txt", ios::out);
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
		GRBVar K[ROUNDS][BLOCK_SIZE];
		GRBVar LL[3][BLOCK_SIZE];
		GRBVar LL1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar O[ROUNDS - 1][BLOCK_SIZE];
		GRBVar OI[ROUNDS - 1][BLOCK_SIZE];
		GRBVar RR1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar C[ROUNDS - 1][BLOCK_SIZE];

		// Set variables 2
		GRBVar K_1[ROUNDS][BLOCK_SIZE];
		GRBVar LL_1[3][BLOCK_SIZE];
		GRBVar LL1_1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar O_1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar OI_1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar RR1_1[ROUNDS - 1][BLOCK_SIZE];
		GRBVar C_1[ROUNDS - 1][BLOCK_SIZE];

		// Set differential variables
		GRBVar DK[ROUNDS][BLOCK_SIZE];
		GRBVar DLL[ROUNDS - 1][BLOCK_SIZE];


		for (int i = 0; i < ROUNDS; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
				DK[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
		
		for (int i = 0; i <= 2; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
				DLL[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);

		
		for (int i = 0; i<ROUNDS - 1; i++)
			for (int j = 0; j<BLOCK_SIZE; j++)
			{
				LL1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				O[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				OI[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				RR1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				C[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);

				LL1_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				O_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				OI_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				RR1_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				C_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}
		for (int i = 0; i < ROUNDS; i++)
			for (int j = 0; j < BLOCK_SIZE; j++) {
				K[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				K_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}

		for (int i = 0; i <= 2; i++)
			for (int j = 0; j < BLOCK_SIZE; j++) {
				LL[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
				LL_1[i][j] = model.addVar(0.0, 1.0, 0.0, GRB_BINARY);
			}

		model.update();
// Building MILP model for key schedule algorithm of SPECK
		for (int i = 1; i < ROUNDS; i++) 
		{
			if (i <= 3) {
				RIGHTSHIFT(env, model, i, LL, i, W0, LL1);
			}
			else if (i >= 4) {
				RIGHTSHIFT(env, model, i, O, i - 3, W0, LL1);
			}
			
				
			Modular_Addition(env, model, i, LL1, K, OI, C);
			LEFTSHIFT(env, model, i, K, i, W1, RR1);
			XORRKEY(env, model, i, RR1, K, i + 1, O);
		}
		for (int r = 0; r < ROUNDS - 1; r++) {
			int cr = 7;
			for (int j = BLOCK_SIZE - 8; j < BLOCK_SIZE; j++) {
				if (bitset<8>(r)[cr] == 0)
					model.addConstr(O[r][j] == OI[r][j]);
				if (bitset<8>(r)[cr] == 1)
					model.addConstr(O[r][j] + OI[r][j] == 1);
				cr--;
			}
			for (int j = 0; j < BLOCK_SIZE - 8; j++)
				model.addConstr(O[r][j] == OI[r][j]);
		}
// Building MILP model for key schedule algorithm of SPECK for the second times		
		for (int i = 1; i < ROUNDS; i++)
		{
			if (i <= 3) {
				RIGHTSHIFT(env, model, i, LL_1, i, W0, LL1_1);
			}
			else if (i >= 4) {
				RIGHTSHIFT(env, model, i, O_1, i - 3, W0, LL1_1);
			}
			Modular_Addition(env, model, i, LL1_1, K_1, OI_1, C_1);
			LEFTSHIFT(env, model, i, K_1, i, W1, RR1_1);
			XORRKEY(env, model, i, RR1_1, K_1, i + 1, O_1);
		}
		for (int r = 0; r < ROUNDS - 1; r++) {
			int cr_1 = 7;
			for (int j = BLOCK_SIZE - 8; j < BLOCK_SIZE; j++) {
				if (bitset<8>(r)[cr_1] == 0)
					model.addConstr(O_1[r][j] == OI_1[r][j]);
				if (bitset<8>(r)[cr_1] == 1)
					model.addConstr(O_1[r][j] + OI_1[r][j] == 1);
				cr_1--;
			}
			for (int j = 0; j < BLOCK_SIZE - 8; j++)
				model.addConstr(O_1[r][j] == OI_1[r][j]);
		}
		
		for (int i = 1; i <= ROUNDS; i++)
			XORR(env, model, i, K, K_1, DK);

		for (int i = 1; i < 4; i++)
			XORR(env, model, i, LL, LL_1, DLL);

		Rounds_Key_Diff(env, model, DK, DLL);
		model.update();
		model.optimize();
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//										   Print the key values 	  							     	//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
			outputFile << "\n\n\n\n the first value:\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (K[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL[1][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL[2][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";

			outputFile << "\n\n\n\n the second value:\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (K_1[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL_1[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL_1[1][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (LL_1[2][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n\n\n\n";

			outputFile << "\n\n\n\n the differential:\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (DK[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (DLL[0][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (DLL[1][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n";
			for (int j = 0; j < BLOCK_SIZE; j++)
				outputFile << (DLL[2][j].get(GRB_DoubleAttr_Xn));
			outputFile << "\n\n\n\n\n";

			outputFile << "K:\n";
			for (int r = 0; r < ROUNDS; r++) {
				for (int j = 0; j < BLOCK_SIZE; j++)
					outputFile << (K[r][j].get(GRB_DoubleAttr_Xn));
				outputFile << "\n";
			}
			outputFile << "\n\n\n";

			outputFile << "K_1:\n";
			for (int r = 0; r < ROUNDS; r++) {
				for (int j = 0; j < BLOCK_SIZE; j++)
					outputFile << (K_1[r][j].get(GRB_DoubleAttr_Xn));
				outputFile << "\n";
			}
			outputFile << "\n\n\n";

			outputFile << "DK:\n";
			for (int r = 0; r < ROUNDS; r++) {
				for (int j = 0; j < BLOCK_SIZE; j++)
					outputFile << (DK[r][j].get(GRB_DoubleAttr_Xn));
				outputFile << "\n";
			}
			outputFile << "\n\n\n";

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
