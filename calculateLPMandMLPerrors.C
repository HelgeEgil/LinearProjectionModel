#include <TTree.h>
#include <TFile.h>
#include <TH1F.h>
#include <TH2F.h>
#include <TCanvas.h>
#include <TVector3.h>
#include <fstream>
#include <TBranch.h>
#include <TGraph.h>
#include <TSpline.h>
#include <TStyle.h>
#include <Math/Vector3D.h>
#include <TRandom3.h>
#include <TLegend.h>
#include <TLatex.h>

// high energy = 230 MeV
// otherwise use 200 MeV parameters from schulte (2008)
#define USEHIGHENERGY

#ifdef  USEHIGHENERGY
#define azero  5.77619e-6
#define aone   2.19784e-7
#define atwo   (-1.23920e-8)
#define athree 3.41725e-9
#define afour  (-2.20283e-10)
#define afive  5.68267e-12
#else
#define azero   7.556e-6
#define aone    4.548e-7
#define atwo    (-5.777e-8)
#define athree  1.301e-8
#define afour   (-9.228e-10)
#define afive   2.687e-11
#endif

#define X_0 36.1

using namespace std;
typedef ROOT::Math::DisplacementVector3D<ROOT::Math::Cartesian3D<double> > XYZVector;

float Sigmat1(float);
float Sigmaz1(float);
float Sigmatz1(float);
float Sigmat2(float, float);
float Sigmaz2(float, float);
float Sigmatz2(float, float);

XYZVector SplineMLP(Double_t t, XYZVector X0, XYZVector X2, XYZVector P0, XYZVector P2, Double_t Lambda0, Double_t Lambda2, Float_t phantomSize) {
   XYZVector P0Lambda, P2Lambda, S;
   Float_t tt = pow(t, 2), ttt = pow(t, 3);

   P0Lambda = P0 * Lambda0 * phantomSize;
   P2Lambda = P2 * Lambda2 * phantomSize;

   S = (2*ttt - 3*tt + 1) * X0 + (ttt - 2*tt + t) * P0Lambda + (-2*ttt + 3*tt) * X2 + (ttt - tt) * P2Lambda;

   return S;
}


void findMLP(Float_t phantomSize = 200, Float_t rotation = -1, Float_t spotsize = -1, Float_t initialEnergy = 230) {
   TFile *f = nullptr;

   if (rotation >= 0) {
      f = new TFile(Form("MC/Output/simpleScanner_energy%.0fMeV_Water_phantom%03.0fmm_rotation%02.0fmrad.root", initialEnergy, phantomSize, rotation));
   }

   else if (spotsize >= 0)  {
      f = new TFile(Form("MC/Output/simpleScanner_energy%.0fMeV_Water_phantom%03.0fmm_spotsize%04.1fmm.root", initialEnergy, phantomSize, spotsize));
   }
   
   else {
      f = new TFile(Form("MC/Output/simpleScanner_energy%.0fMeV_Water_phantom%03.0fmm.root", initialEnergy, phantomSize));
   }
   

   TTree *tree = (TTree*) f->Get("Hits");

   if (!tree) exit(0);

   // Set these parameters
   Int_t       printed = 0;
   const Int_t eventsToUse = 10000;
   Float_t     sigmaTheta = 0; // scattering between last two tracker layers, rad. 0 = ideal detector
   Float_t     sigmaPos = 0; // Position unc. in tracking layers, mm. 0 = ideal detector
   Float_t     sourceToX0dist = 100;
   Float_t     d_entry = 10;
   Float_t     d_exit = 10;
   Float_t     d_T = 10; // m between trackers
   Int_t       maxAcc = 10; // Number of X1 histories to plot
   Bool_t      kModelUncertainties = true; // Model the tracker uncertainties in MLP model

   // initializations
   TRandom3  * gRandom = new TRandom3(0);
   Float_t     x, y, z, edep, sum_edep = 0, residualEnergy = 0;
   Int_t       eventID, parentID, lastEID = -1;
   XYZVector   Xp0, Xp1, Xp2, Xp3, X0, X2, X0LPM, X0err, X0tps, P0, P0tps, P2, S, P2prime, X2prime, scat; // Xp are the plane coordinates, X are the tracker coordinates (X2 = (Xp1 + Xp2) / 2)
   XYZVector   projectedPathX0, projectedPath, X0krah, P0krah, X0errNaive, X0errKrah;
   XYZVector   scatXp2, scatXp3, Xp2prime, Xp3prime, P2gaus;
   XYZVector   X0cm, X2cm;
   XYZVector   projectToHullX0, projectToHullX2;
   Float_t     wepl, wet, Lambda0, Lambda2;
   Float_t     theta_x_0, theta_y_0, theta_x_2, theta_y_2, tps_theta_x_0, tps_theta_y_0;
   ifstream    in;
   TSpline3  * splineMCx, * splineMCy, * splineMLPx, * splineMLPy;
   TSpline3  * splineMLPKrahx, * splineMLPKrahy, * splineMLPLPMx, * splineMLPLPMy;
   TSpline3  * splineMLPNoTrkx, * splineMLPNoTrky; 
   Double_t    arSplineMCx[1000], arSplineMCy[1000], arSplineMCz[1000], arSplineMLPx[1000], arSplineMLPy[1000], arSplineMLPz[1000];
   Double_t    arSplineMLPNoTrkx[1000], arSplineMLPNoTrky[1000], arSplineMLPLPMx[1000], arSplineMLPLPMy[1000];
   Double_t    arSplineMLPKrahx[1000], arSplineMLPKrahy[1000]; 
   Int_t       idxSplineMC = 0, idxSplineMLP = 0, idxSplineMLPkrah = 0;
   Double_t    differenceArrayZ[1000];
   Double_t    differenceArrayDiff[1000] = {};
   Double_t    differenceArrayDiffNoTrk[1000] = {};
   Double_t    differenceArrayDiffKrah[1000] = {};
   Double_t    differenceArrayDiffLPM[1000] = {};
   Float_t     theta_x_gaus, theta_y_gaus, energy, range, energyFilter = 0, sigmaFilter = 1e5;
   Int_t       nInDifferenceArray = 0, idxDifferenceArray = 0, idxWater = 0;
   Double_t    energiesWater[500], rangesWater[500];
   Double_t    aPosMCx[10000], aPosMCy[10000], aPosMCz[10000];
   Double_t    aPosMLPx[10000], aPosMLPy[10000], aPosMLPz[10000];
   Double_t    aPosMLPNoTrkx[10000], aPosMLPNoTrky[10000];
   Double_t    aPosMLPKrahx[10000], aPosMLPKrahy[10000];
   Double_t    aPosMLPKrahz[10000], arSplineMLPKrahz[1000];
   Double_t    aPosMLPLPMx[10000], aPosMLPLPMy[10000];
   Int_t       volumeID[10];
   TBranch   * b_volumeID;
   Int_t       aIdxMC = 0, aIdxMLP = 0, aIdxMLPkrah = 0;
   Bool_t      stop = false; 
   Float_t     spotSizeAtX0;
   Float_t     w, w2, dxy, angle, AX, AP;
   Double_t    step_length, posz, st2, sz2, stz2, st1, sz1, stz1;
   Double_t    determinant_1, determinant_2, determinant_C12;
   Double_t    d_source, s_pos, s_angle, X_mlp, Y_mlp, theta_X_mlp, theta_Y_mlp;
   Float_t     scatter_2[4];
   Float_t     scatter_1[4];
   Float_t     sigma_beam[4];
   double      R_0[4] = {0};
   double      R_0_transpose[4] = {0};
   double      R_1_inverse[4] = {0};
   double      R_1_inverse_transpose[4] = {0};
   double      y_0[2] = {0};
   double      y_2[2] = {0};
   double      C1_1[4] = {0};
   double      C1_2[4] = {0};
   double      C1[4] = {0};
   double      C2_1[4] = {0};
   double      C2_2[4] = {0};
   double      C2[4] = {0};
   double      C12[4];
   double      C12_inverse[4] = {0};
   
   double      first_first[4] = {0};
   double      second_first[4] = {0};
   double      first_second[2] = {0};
   double      second_second[2] = {0};

   double      first[2] = {0};
   double      second[2] = {0};
   double      T_out[4];
   double      T_out_transpose[4];
   double      sigma_out[4];
   double      S_out_inverse[4];
   double      S_out_inverse_transpose[4];
   double      track_uncert_1[4];
   double      track_uncert[4];
   int         a; // iterator for matrix operations

   // Spot size is defined at 100 mm upstream for the trackers, with a 2 mrad divergence
   // This is a parametric calculation of the beam spot size at the X0 position
   if (spotsize < 0) spotSizeAtX0 = 3.15;
   else              spotSizeAtX0 = 0.9869 * spotsize + 0.1985;

   // Load Energy <-> Range spline
   in.open("Data/WaterPSTAR.csv");
   while (1) {
      in >> energy >> range;
      if (!in.good()) break;
      rangesWater[idxWater] = range*10; // [mm]
      energiesWater[idxWater++] = energy;
   }
   in.close();
   TSpline3 *splineWater = new TSpline3("splineWater", energiesWater, rangesWater, idxWater);

   TH1F *hResEnergy = new TH1F("hResEnergy", "Residual energy in calorimeter;Energy [MeV];Entries", 300, 0, 250);

   TH2F *hErrorNaive = new TH2F("hErrorNaive", "Beamspot uncertainty (assume point beam);X position [mm];Y position [mm]", 100, -25, 25, 100, -25, 25);
   TH2F *hErrorKrah = new TH2F("hErrorKrah", "Beamspot uncertainty (assume point beam);X position [mm];Y position [mm]", 100, -25, 25, 100, -25, 25);
   TH2F *hErrorLPM = new TH2F("hErrorLPM", Form("Beamspot uncertainty (LPM);X position [mm];Y position [mm]"), 100, -25, 25, 100, -25, 25);

   tree->SetBranchAddress("posX", &x);
   tree->SetBranchAddress("posY", &y);
   tree->SetBranchAddress("posZ", &z);
   tree->SetBranchAddress("edep", &edep);
   tree->SetBranchAddress("eventID", &eventID);
   tree->SetBranchAddress("parentID", &parentID);
   tree->SetBranchAddress("volumeID", volumeID, &b_volumeID);
  
   if (rotation >= 0) { // defined, use actual number (mrad rotated about X)
      tps_theta_x_0 = 0;
      tps_theta_y_0 = -rotation / 1000;
   }
   else { // rotation = -1 means not defined, not interLPMing, etc ... it's zero
      tps_theta_x_0 = 0;
      tps_theta_y_0 = 0;
   }
   
   P0tps.SetCoordinates(atan(tps_theta_x_0), atan(tps_theta_y_0), 1);
   X0tps.SetCoordinates(atan(tps_theta_x_0) * (sourceToX0dist + d_entry), atan(tps_theta_y_0) * (sourceToX0dist + d_entry), 0);

   for (Int_t i=0; i<tree->GetEntries(); ++i) {
      tree->GetEntry(i);

      if (eventID > eventsToUse) stop = true;

      if (lastEID < 0) {
         lastEID = eventID;
         sum_edep = edep;
         residualEnergy = 0;
      }

      if (lastEID != eventID) { // Particle history fully loaded
         // Add scattering and pixel uncertainty
         scatXp2.SetCoordinates(gRandom->Gaus(0, sigmaPos), gRandom->Gaus(0, sigmaPos), 0);
         scatXp3.SetCoordinates(gRandom->Gaus(0, sigmaPos), gRandom->Gaus(0, sigmaPos), 0);
         P2 = (Xp3 - Xp2) / (Xp3.Z() - Xp2.Z());
         theta_x_gaus = gRandom->Gaus(tan(P2.X()), sigmaTheta);
         theta_y_gaus = gRandom->Gaus(tan(P2.Y()), sigmaTheta);
         P2gaus.SetCoordinates(atan(theta_x_gaus), atan(theta_y_gaus), 1);
         Xp2prime = Xp2 + scatXp2;
         Xp3prime = Xp2 + P2gaus * d_T + scatXp3;

         // Redefine X2, P2 to account for different scattering uncertainties
         X0 = Xp1;
         X2 = Xp2prime;
         P0 = (Xp1 - Xp0) / (Xp1.Z() - Xp0.Z());
         P2 = (Xp3prime - Xp2prime) / (Xp3prime.Z() - Xp2prime.Z());

         P2prime = P2 - P0tps;
         P2prime.SetZ(1);

         projectToHullX0.SetCoordinates(d_entry * tan(P0.X()), d_entry * tan(P0.Y()), d_entry);
         projectToHullX2.SetCoordinates(d_exit * tan(P2.X()), d_exit * tan(P2.Y()), d_exit);
         X0 += projectToHullX0;
         X2 -= projectToHullX2;

         // MLP parameters defined for cm, so use cm there
         X0cm = X0tps / 10;
         X2cm = X2 / 10;

         wepl = splineWater->Eval(initialEnergy);
         wet = wepl - splineWater->Eval(residualEnergy);
         w = wet / wepl;
         w2 = pow(wet / wepl, 2);
        
         AX = exp(2.5073 - 6.3858*w + 0.4913*w2);
         AP = exp(1.8175 - 5.9708*w - 0.8158*w2); 
         
         dxy = sqrt(pow(P2prime.X(), 2) + pow(P2prime.Y(), 2));
         angle = fabs(atan2(dxy,1)) * 1000;

         sigmaFilter = exp(2.18 + 8.08*w - 12.25*w2 + 7.07*pow(w,3));
         
         if (hResEnergy->GetEntries() > 5) {
            energyFilter = hResEnergy->GetMean() * 0.9;
         }
         else energyFilter = 0;

         if (residualEnergy > energyFilter && angle < sigmaFilter) {
            hResEnergy->Fill(residualEnergy);
            step_length = (X2cm.Z() - X0cm.Z()) / 512;
            
            for (float posz = X0cm.Z() + step_length; posz < X2cm.Z(); posz += step_length) {
               d_source = 200; // assume to first tracker layer -- is this valid for all phantom sizes / spot sizes
               s_pos = pow(spotSizeAtX0/10, 2); // cm
               s_angle = pow(0.002, 2); // div. so 2 mrad

               sigma_beam[0] = s_pos;
               sigma_beam[1] = s_pos/d_source;
               sigma_beam[2] = s_pos/d_source;
               sigma_beam[3] = s_pos/(pow(d_source,2)) + s_angle;

               float s_pos_out = sigmaPos / 10; // in cm LLU 66 um, Bergen 5 um
               float s_scat_out = sigmaTheta; // rad LLU 10 mrad, Bergen 7 mrad

               if (!kModelUncertainties) {
                  s_pos_out = 0;
                  s_scat_out = 0;   
               }

               T_out[0] = 0;
               T_out[1] = 0;
               T_out[2] = -1/(d_T/10); // mm -> cm
               T_out[3] = 1/(d_T/10);

               T_out_transpose[0] = T_out[0];
               T_out_transpose[1] = T_out[2];
               T_out_transpose[2] = T_out[1];
               T_out_transpose[3] = T_out[3];

               sigma_out[0] = pow(s_pos_out, 2) * ((T_out_transpose[0] * T_out[0]) + (T_out_transpose[1]*T_out[2]));
               sigma_out[1] = pow(s_pos_out, 2) * ((T_out_transpose[0] * T_out[1]) + (T_out_transpose[1]*T_out[3]));
               sigma_out[2] = pow(s_pos_out, 2) * ((T_out_transpose[2] * T_out[0]) + (T_out_transpose[3]*T_out[2]));
               sigma_out[3] = pow(s_pos_out, 2) * ((T_out_transpose[2] * T_out[1]) + (T_out_transpose[3]*T_out[3])) + pow(s_scat_out, 2);

               S_out_inverse[0] = 1;
               S_out_inverse[1] = -d_exit/10; // mm -> cm
               S_out_inverse[2] = 0;
               S_out_inverse[3] = 1;

               S_out_inverse_transpose[0] = 1;
               S_out_inverse_transpose[1] = 0;
               S_out_inverse_transpose[2] = -d_exit/10;
               S_out_inverse_transpose[3] = 1;

               track_uncert_1[0] = (sigma_out[0] * S_out_inverse_transpose[0]) + (sigma_out[1] * S_out_inverse_transpose[2]);
               track_uncert_1[1] = (sigma_out[0] * S_out_inverse_transpose[1]) + (sigma_out[1] * S_out_inverse_transpose[3]);
               track_uncert_1[2] = (sigma_out[2] * S_out_inverse_transpose[0]) + (sigma_out[3] * S_out_inverse_transpose[2]);
               track_uncert_1[3] = (sigma_out[2] * S_out_inverse_transpose[1]) + (sigma_out[3] * S_out_inverse_transpose[3]);

               track_uncert[0] = (S_out_inverse[0] * track_uncert_1[0]) + (S_out_inverse[1] * track_uncert_1[2]);
               track_uncert[1] = (S_out_inverse[0] * track_uncert_1[1]) + (S_out_inverse[1] * track_uncert_1[3]);
               track_uncert[2] = (S_out_inverse[2] * track_uncert_1[0]) + (S_out_inverse[3] * track_uncert_1[2]);
               track_uncert[3] = (S_out_inverse[2] * track_uncert_1[1]) + (S_out_inverse[3] * track_uncert_1[3]);

               sz1 = Sigmaz1(posz - X0cm.Z());
               st1 = Sigmat1(posz - X0cm.Z());
               stz1 = Sigmatz1(posz - X0cm.Z());
               
               sz2 = Sigmaz2(X2cm.Z() - X0cm.Z(), posz - X0cm.Z());
               stz2 = Sigmatz2(X2cm.Z() - X0cm.Z(), posz - X0cm.Z());
               st2 = Sigmat2(X2cm.Z() - X0cm.Z(), posz - X0cm.Z());

               R_0[0] = 1;
               R_0[1] = posz - X0cm.Z();
               R_0[2] = 0;
               R_0[3] = 1;

               R_0_transpose[0] = 1;
               R_0_transpose[1] = 0;
               R_0_transpose[2] = posz - X0cm.Z();
               R_0_transpose[3] = 1;

               R_1_inverse[0] = 1;
               R_1_inverse[1] = -(X2cm.Z() - posz); // ok
               R_1_inverse[2] = 0;
               R_1_inverse[3] = 1;

               R_1_inverse_transpose[0] = 1;
               R_1_inverse_transpose[1] = 0;
               R_1_inverse_transpose[2] = -(X2cm.Z() - posz);
               R_1_inverse_transpose[3] = 1;
         
               scatter_1[0] = sz1;
               scatter_1[1] = stz1;
               scatter_1[2] = stz1;
               scatter_1[3] = st1;

               scatter_2[0] = sz2;
               scatter_2[1] = stz2;
               scatter_2[2] = stz2;
               scatter_2[3] = st2;

               // pre-factors C1 + C2 as in Krah et al. (2018)
               C1_1[0] = (sigma_beam[0] * R_0_transpose[0]) + (sigma_beam[1] * R_0_transpose[2]);
               C1_1[1] = (sigma_beam[0] * R_0_transpose[1]) + (sigma_beam[1] * R_0_transpose[3]);
               C1_1[2] = (sigma_beam[2] * R_0_transpose[0]) + (sigma_beam[3] * R_0_transpose[2]);
               C1_1[3] = (sigma_beam[2] * R_0_transpose[1]) + (sigma_beam[3] * R_0_transpose[3]);

               C1_2[0] = (R_0[0] * C1_1[0]) + (R_0[1] * C1_1[2]);
               C1_2[1] = (R_0[0] * C1_1[1]) + (R_0[1] * C1_1[3]);
               C1_2[2] = (R_0[2] * C1_1[0]) + (R_0[3] * C1_1[2]);
               C1_2[3] = (R_0[2] * C1_1[1]) + (R_0[3] * C1_1[3]);

               for (a=0; a<4; a++) C1[a] = C1_2[a] + scatter_1[a];
               
               C2_1[0] = (track_uncert[0] * R_1_inverse_transpose[0]) + (track_uncert[1] * R_1_inverse_transpose[2]);
               C2_1[1] = (track_uncert[0] * R_1_inverse_transpose[1]) + (track_uncert[1] * R_1_inverse_transpose[3]);
               C2_1[2] = (track_uncert[2] * R_1_inverse_transpose[0]) + (track_uncert[3] * R_1_inverse_transpose[2]);
               C2_1[3] = (track_uncert[2] * R_1_inverse_transpose[1]) + (track_uncert[3] * R_1_inverse_transpose[3]);

               C2_2[0] = (scatter_2[0] * R_1_inverse_transpose[0]) + (scatter_2[1] * R_1_inverse_transpose[2]);
               C2_2[1] = (scatter_2[0] * R_1_inverse_transpose[1]) + (scatter_2[1] * R_1_inverse_transpose[3]);
               C2_2[2] = (scatter_2[2] * R_1_inverse_transpose[0]) + (scatter_2[3] * R_1_inverse_transpose[2]);
               C2_2[3] = (scatter_2[2] * R_1_inverse_transpose[1]) + (scatter_2[3] * R_1_inverse_transpose[3]);
           
               C2[0] = (R_1_inverse[0] * C2_1[0]) + (R_1_inverse[1] * C2_1[2]) + (R_1_inverse[0] * C2_2[0]) + (R_1_inverse[1] * C2_2[2]);
               C2[1] = (R_1_inverse[0] * C2_1[1]) + (R_1_inverse[1] * C2_1[3]) + (R_1_inverse[0] * C2_2[1]) + (R_1_inverse[1] * C2_2[3]);
               C2[2] = (R_1_inverse[2] * C2_1[0]) + (R_1_inverse[3] * C2_1[2]) + (R_1_inverse[2] * C2_2[0]) + (R_1_inverse[3] * C2_2[2]);
               C2[3] = (R_1_inverse[2] * C2_1[1]) + (R_1_inverse[3] * C2_1[3]) + (R_1_inverse[2] * C2_2[1]) + (R_1_inverse[3] * C2_2[3]);

               for (a=0; a<4; a++) C12[a] = C1[a] + C2[a];

               // invert to get the complete prefactor (C1 + C2)^-1
               determinant_C12 = (C12[0] * C12[3]) - (C12[1] * C12[2]);
               C12_inverse[0] =  C12[3] / determinant_C12;
               C12_inverse[1] = -C12[1] / determinant_C12;
               C12_inverse[2] = -C12[2] / determinant_C12;
               C12_inverse[3] =  C12[0] / determinant_C12;

               first_first[0] = (C2[0] * C12_inverse[0]) + (C2[1] * C12_inverse[2]);
               first_first[1] = (C2[0] * C12_inverse[1]) + (C2[1] * C12_inverse[3]);
               first_first[2] = (C2[2] * C12_inverse[0]) + (C2[3] * C12_inverse[2]);
               first_first[3] = (C2[2] * C12_inverse[1]) + (C2[3] * C12_inverse[3]);

               second_first[0] = (C1[0] * C12_inverse[0]) + (C1[1] * C12_inverse[2]);
               second_first[1] = (C1[0] * C12_inverse[1]) + (C1[1] * C12_inverse[3]);
               second_first[2] = (C1[2] * C12_inverse[0]) + (C1[3] * C12_inverse[2]);
               second_first[3] = (C1[2] * C12_inverse[1]) + (C1[3] * C12_inverse[3]);

               y_0[0] = X0cm.X();
               y_0[1] = tan(P0tps.X());
               y_2[0] = X2cm.X();
               y_2[1] = tan(P2.X());
      
               first_second[0] = (R_0[0] * y_0[0]) + (R_0[1] * y_0[1]);
               first_second[1] = (R_0[2] * y_0[0]) + (R_0[3] * y_0[1]);
               second_second[0] = (R_1_inverse[0] * y_2[0]) + (R_1_inverse[1] * y_2[1]);
               second_second[1] = (R_1_inverse[2] * y_2[0]) + (R_1_inverse[3] * y_2[1]);

               first[0] = (first_first[0] * first_second[0]) + (first_first[1] * first_second[1]);
               first[1] = (first_first[2] * first_second[0]) + (first_first[3] * first_second[1]);
               second[0] = (second_first[0] * second_second[0]) + (second_first[1] * second_second[1]);
               second[1] = (second_first[2] * second_second[0]) + (second_first[3] * second_second[1]);

               X_mlp = first[0] + second[0]; // the X0 position! 

               // now do the y value
               y_0[0] = X0cm.Y();
               y_0[1] = tan(P0tps.Y());
               y_2[0] = X2cm.Y();
               y_2[1] = tan(P2.Y());
               
               first_second[0] = (R_0[0] * y_0[0]) + (R_0[1] * y_0[1]);
               first_second[1] = (R_0[2] * y_0[0]) + (R_0[3] * y_0[1]);
               second_second[0] = (R_1_inverse[0] * y_2[0]) + (R_1_inverse[1] * y_2[1]);
               second_second[1] = (R_1_inverse[2] * y_2[0]) + (R_1_inverse[3] * y_2[1]);

               first[0] = (first_first[0] * first_second[0]) + (first_first[1] * first_second[1]);
               first[1] = (first_first[2] * first_second[0]) + (first_first[3] * first_second[1]);
               second[0] = (second_first[0] * second_second[0]) + (second_first[1] * second_second[1]);
               second[1] = (second_first[2] * second_second[0]) + (second_first[3] * second_second[1]);

               Y_mlp = first[0] + second[0]; // the X0 position!

               // Add all the positions to the spline matrix
               arSplineMLPKrahz[idxSplineMLPkrah] = posz*10;
               arSplineMLPKrahx[idxSplineMLPkrah] = X_mlp*10;
               arSplineMLPKrahy[idxSplineMLPkrah++] = Y_mlp*10;

               // and the individual tracks
               if (lastEID < maxAcc) {
                  aPosMLPKrahz[aIdxMLPkrah] = posz*10;
                  aPosMLPKrahx[aIdxMLPkrah] = X_mlp*10;
                  aPosMLPKrahy[aIdxMLPkrah++] = Y_mlp*10;
               }
            } // done looping over phantom

            X2prime = X2 - X0tps - phantomSize * P0tps;

            X0LPM = X2prime * AX/(pow(spotSizeAtX0,-2)+AX) - P2prime * AP/(pow(spotSizeAtX0,-2)+AX) * phantomSize + X0tps;
            X0LPM.SetZ(0);

            X0err = X0LPM - X0;
            X0errNaive = X0tps - X0;
            X0errKrah = X0krah - X0;

            hErrorNaive->Fill(X0errNaive.X(), X0errNaive.Y());
            hErrorLPM->Fill(X0err.X(), X0err.Y());
            hErrorKrah->Fill(X0errKrah.X(), X0errKrah.Y());

            // Find lambda values using polynomial in Fig. 4 in Fekete et al. 2015
            Lambda0 = 1.01 + 0.43 * w2;
            Lambda2 = 0.99 - 0.46 * w2;

            for (Float_t t=0; t<1; t += 0.01) {
               S = SplineMLP(t, X0, X2, P0, P2, Lambda0, Lambda2, phantomSize); // perfect detector

               if (lastEID < maxAcc) {
                  aPosMLPx[aIdxMLP] = S.X();
                  aPosMLPy[aIdxMLP] = S.Y();
                  aPosMLPz[aIdxMLP] = S.Z();
               }
               
               arSplineMLPx[idxSplineMLP] = S.X(); 
               arSplineMLPy[idxSplineMLP] = S.Y();
               arSplineMLPz[idxSplineMLP] = S.Z();

               S = SplineMLP(t, X0tps, X2, P0tps, P2, Lambda0, Lambda2, phantomSize); // Naive

               arSplineMLPNoTrkx[idxSplineMLP] = S.X();
               arSplineMLPNoTrky[idxSplineMLP] = S.Y();

               if (lastEID < maxAcc) {
                  aPosMLPNoTrkx[aIdxMLP] = S.X();
                  aPosMLPNoTrky[aIdxMLP] = S.Y();
               }
               S = SplineMLP(t, X0LPM, X2, P0tps, P2, Lambda0, Lambda2, phantomSize); // LPM

               arSplineMLPLPMx[idxSplineMLP] = S.X();
               arSplineMLPLPMy[idxSplineMLP++] = S.Y();

               if (lastEID < maxAcc) {
                  aPosMLPLPMy[aIdxMLP] = S.Y();
                  aPosMLPLPMx[aIdxMLP++] = S.X();
               }
            }

            // Compare MC and MLP here
            // 1) Make splines to compare at same Z
            splineMCx  = new TSpline3("splineMCx", arSplineMCz, arSplineMCx, idxSplineMC);
            splineMCy  = new TSpline3("splineMCy", arSplineMCz, arSplineMCy, idxSplineMC);
            splineMLPx = new TSpline3("splineMLPx", arSplineMLPz, arSplineMLPx, idxSplineMLP);
            splineMLPy = new TSpline3("splineMLPy", arSplineMLPz, arSplineMLPy, idxSplineMLP);
            splineMLPLPMx = new TSpline3("splineMLPLPMx", arSplineMLPz, arSplineMLPLPMx, idxSplineMLP);
            splineMLPLPMy = new TSpline3("splineMLPLPMy", arSplineMLPz, arSplineMLPLPMy, idxSplineMLP);
            splineMLPNoTrkx = new TSpline3("splineMLPNoTrkx", arSplineMLPz, arSplineMLPNoTrkx, idxSplineMLP);
            splineMLPNoTrky = new TSpline3("splineMLPNoTrky", arSplineMLPz, arSplineMLPNoTrky, idxSplineMLP);
            splineMLPKrahx = new TSpline3("splineMLPKrahx", arSplineMLPKrahz, arSplineMLPKrahx, idxSplineMLPkrah);
            splineMLPKrahy = new TSpline3("splineMLPKrahy", arSplineMLPKrahz, arSplineMLPKrahy, idxSplineMLPkrah);

            // 2) Sweep Z values and add the absolute difference to an array
            float rvalue = splineMCx->Eval(0);
            if (!isnan(rvalue)) {
               Double_t diff_x, diff_y;
               idxDifferenceArray = 0; // Sweep each time
               nInDifferenceArray++; // To average at end
               for (Double_t zSweep = 0; zSweep <= phantomSize; zSweep += 0.5) { // Keep Sweep increment high to speed up!
                  differenceArrayZ[idxDifferenceArray] = zSweep;
                  diff_x = fabs(splineMCx->Eval(zSweep) - splineMLPx->Eval(zSweep));
                  diff_y = fabs(splineMCy->Eval(zSweep) - splineMLPy->Eval(zSweep));
                  differenceArrayDiff[idxDifferenceArray] += sqrt(pow(diff_x, 2) + pow(diff_y, 2));

                  diff_x = fabs(splineMCx->Eval(zSweep) - splineMLPKrahx->Eval(zSweep));
                  diff_y = fabs(splineMCy->Eval(zSweep) - splineMLPKrahy->Eval(zSweep));
                  differenceArrayDiffKrah[idxDifferenceArray] += sqrt(pow(diff_x, 2) + pow(diff_y, 2));
                  
                  diff_x = fabs(splineMCx->Eval(zSweep) - splineMLPNoTrkx->Eval(zSweep));
                  diff_y = fabs(splineMCy->Eval(zSweep) - splineMLPNoTrky->Eval(zSweep));
                  differenceArrayDiffNoTrk[idxDifferenceArray] += sqrt(pow(diff_x, 2) + pow(diff_y, 2));

                  diff_x = fabs(splineMCx->Eval(zSweep) - splineMLPLPMx->Eval(zSweep));
                  diff_y = fabs(splineMCy->Eval(zSweep) - splineMLPLPMy->Eval(zSweep));
                  differenceArrayDiffLPM[idxDifferenceArray++] += sqrt(pow(diff_x, 2) + pow(diff_y, 2));
               }
            }

            delete splineMCx;
            delete splineMCy;
            delete splineMLPx;
            delete splineMLPy;
            delete splineMLPKrahx;
            delete splineMLPKrahy;
            delete splineMLPLPMx;
            delete splineMLPLPMy;
         }
         
         if (stop) break;

         // Reset counters for next primary
         sum_edep = edep;
         residualEnergy = 0;
         lastEID = eventID;
         idxSplineMLP = 0;
         idxSplineMLPkrah = 0;
         idxSplineMC = 0;
      }

      else { // Still following the same particle
         if (parentID == 0) { sum_edep += edep; }
         lastEID = eventID;
      }

      if (parentID == 0) {
         if       (volumeID[2] == 0) Xp0.SetCoordinates(x,y,z+phantomSize/2);
         else if  (volumeID[2] == 1) Xp1.SetCoordinates(x,y,z+phantomSize/2);
         else if  (volumeID[2] == 2) Xp2.SetCoordinates(x,y,z+phantomSize/2);
         else if  (volumeID[2] == 3) Xp3.SetCoordinates(x,y,z+phantomSize/2);
         else if  (volumeID[2] == 5) residualEnergy += edep;


         if  (volumeID[2] < 5) {
            arSplineMCx[idxSplineMC] = x;
            arSplineMCy[idxSplineMC] = y;
            arSplineMCz[idxSplineMC++] = z+phantomSize/2;
            
            if (eventID < maxAcc) {
               aPosMCx[aIdxMC] = x;
               aPosMCy[aIdxMC] = y;
               aPosMCz[aIdxMC++] = z+phantomSize/2;
            }
         }
      }
   }

   TCanvas *c0 = new TCanvas("c0", "Residual Energy", 1500, 1000);
   hResEnergy->Draw();

   TCanvas *c1 = new TCanvas("c1", "MLP estimation", 1000, 1000);
   TPad *pad1 = new TPad("pad1", "pad1", 0.005, 0, 0.5235, .995);
   TPad *pad2 = new TPad("pad2", "pad2", .5245, 0, 0.995, .995);

   pad1->Divide(1, 2, 1e-5, 1e-5);
   pad2->Divide(1, 2, 1e-5, 1e-5);

   pad1->Draw(); pad2->Draw(); //pad3->Draw(); pad4->Draw();

   pad1->cd(1);
   TGraph *gMC = new TGraph(aIdxMC, aPosMCz, aPosMCy);
   TGraph *gMCy = new TGraph(aIdxMC, aPosMCz, aPosMCy);
   TGraph *gMLP = new TGraph(aIdxMLP, aPosMLPz, aPosMLPy);
   TGraph *gMLPy = new TGraph(aIdxMLP, aPosMLPz, aPosMLPy);
   gMC->SetMarkerStyle(21);
   gMLP->SetMarkerStyle(21);
   gMC->SetMarkerSize(0.3);
   gMLP->SetMarkerSize(0.3);
   gMC->SetMarkerColor(kRed);
   gMLP->SetMarkerColor(kBlue);
   gMC->Draw("AP");
   gMLP->Draw("P");
   gMC->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMLP->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMC->GetYaxis()->SetRangeUser(-11, 7);
   gMLP->GetYaxis()->SetRangeUser(-11, 7);
   gMC->SetTitle("Perfect knowledge + CSP;Depth [mm];X position [mm]");

   pad2->cd(1);
   TGraph *gMCNoTrk = new TGraph(aIdxMC, aPosMCz, aPosMCy);
   TGraph *gMLPNoTrk = new TGraph(aIdxMLP, aPosMLPz, aPosMLPNoTrky);
   gMLPNoTrk->SetMarkerStyle(21);
   gMLPNoTrk->SetMarkerColor(kBlue);
   gMCNoTrk->SetMarkerStyle(21);
   gMCNoTrk->SetMarkerColor(kRed);
   gMCNoTrk->SetMarkerSize(0.3);
   gMLPNoTrk->SetMarkerSize(0.3);
   gMCNoTrk->Draw("AP");
   gMLPNoTrk->Draw("P");
   gMCNoTrk->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMLPNoTrk->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMCNoTrk->GetYaxis()->SetRangeUser(-11, 7);
   gMLPNoTrk->GetYaxis()->SetRangeUser(-11, 7);
   gMCNoTrk->SetTitle("TPS Position + CSP;Depth [mm];X position [mm]");

   pad1->cd(2);
   TGraph *gMCKrah = new TGraph(aIdxMC, aPosMCz, aPosMCy);
   TGraph *gMLPKrah = new TGraph(aIdxMLPkrah, aPosMLPKrahz, aPosMLPKrahy);
   gMLPKrah->SetMarkerStyle(21);
   gMLPKrah->SetMarkerColor(kBlue);
   gMCKrah->SetMarkerStyle(21);
   gMCKrah->SetMarkerColor(kRed);
   gMCKrah->SetMarkerSize(0.3);
   gMLPKrah->SetMarkerSize(0.3);
   gMCKrah->Draw("AP");
   gMLPKrah->Draw("P");
   gMCKrah->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMCKrah->GetXaxis()->SetNdivisions(509);
   gMCKrah->GetYaxis()->SetRangeUser(-11, 7);
   gMCKrah->SetTitle("Bayesian Most Likely Path;Depth [mm];X position [mm]");
   
   pad2->cd(2);
   TGraph *gMCLPM = new TGraph(aIdxMC, aPosMCz, aPosMCy);
   TGraph *gMLPLPM = new TGraph(aIdxMLP, aPosMLPz, aPosMLPLPMy);
   gMLPLPM->SetMarkerStyle(21);
   gMLPLPM->SetMarkerColor(kBlue);
   gMCLPM->SetMarkerStyle(21);
   gMCLPM->SetMarkerColor(kRed);
   gMCLPM->SetMarkerSize(0.3);
   gMLPLPM->SetMarkerSize(0.3);
   gMCLPM->Draw("AP");
   gMLPLPM->Draw("P");
   gMCLPM->GetXaxis()->SetRangeUser(-30, phantomSize+30);
   gMCLPM->GetXaxis()->SetNdivisions(509);
   gMCLPM->GetYaxis()->SetRangeUser(-11, 7);
   gMCLPM->SetTitle(" Linear Projection Model + CSP;Depth [mm];X position [mm]");

   TCanvas *c = new TCanvas("c", "Beam spot estimation", 1500, 1000);
   c->Divide(3, 1, 0.001, 0.001);

   c->cd(1);
   hErrorNaive->Draw("COLZ");
   c->cd(2);
   hErrorLPM->Draw("COLZ");
   c->cd(3);
   hErrorKrah->Draw("COLZ");

   printf("Normalizing the %d indexes of differenceArray from %d.\n", idxDifferenceArray, nInDifferenceArray);
   for (Int_t i=0; i<idxDifferenceArray; i++) {
      differenceArrayDiff[i] /= nInDifferenceArray;
      differenceArrayDiffNoTrk[i]  /= nInDifferenceArray;
      differenceArrayDiffKrah[i]  /= nInDifferenceArray;
      differenceArrayDiffLPM[i] /= nInDifferenceArray;
   }

   TCanvas *c2 = new TCanvas("c2", "MC vs MLP difference", 1500, 1200);
   TGraph *gDifferencePerfect = new TGraph(idxDifferenceArray, differenceArrayZ, differenceArrayDiff);
   TGraph *gDifferenceNoTrk = new TGraph(idxDifferenceArray, differenceArrayZ, differenceArrayDiffNoTrk);
   TGraph *gDifferenceKrah = new TGraph(idxDifferenceArray, differenceArrayZ, differenceArrayDiffKrah);
   TGraph *gDifferenceLPM = new TGraph(idxDifferenceArray, differenceArrayZ, differenceArrayDiffLPM);

   gDifferencePerfect->SetTitle(";Depth in phantom [mm];Error | X_{1}^{opt} - X_{1}^{MC} | [mm]");
   gDifferencePerfect->SetLineColor(kRed);
   gDifferencePerfect->SetLineWidth(4);
   gDifferenceNoTrk->SetLineColor(kBlack);
   gDifferenceNoTrk->SetLineWidth(4);
   gDifferenceKrah->SetLineColor(kOrange+2);
   gDifferenceKrah->SetLineWidth(4);
   gDifferenceLPM->SetLineColor(kBlue);
   gDifferenceLPM->SetLineWidth(4);
   gDifferencePerfect->Draw("AL");
   gDifferenceNoTrk->Draw("L");
   gDifferenceKrah->Draw("L");
   gDifferenceLPM->Draw("L");
   gDifferencePerfect->GetYaxis()->SetRangeUser(0,4.5);

   TLatex *lat = new TLatex();
   lat->SetTextSize(0.05);
   lat->DrawLatex(20,gDifferencePerfect->Eval(20), "X_{1}^{MC}");
   lat->DrawLatex(20,gDifferenceNoTrk->Eval(20), "X_{1}^{TPS}");
   lat->DrawLatex(20,gDifferenceKrah->Eval(20), "X_{1}^{MLP}");
   lat->DrawLatex(20,gDifferenceLPM->Eval(20), "X_{1}^{LPM}");

   Float_t sigmaNoTrk = (hErrorNaive->GetStdDev(1) + hErrorNaive->GetStdDev(2)) / 2;
   Float_t sigmaLPM = (hErrorLPM->GetStdDev(1) + hErrorLPM->GetStdDev(2)) / 2;

   if (spotsize >= 0) {
      ofstream file(Form("Output/MLPerror_energy%.0fMeV_Water_spotsize_krah.csv", initialEnergy), ofstream::out | ofstream::app);
      file << phantomSize << " " <<  spotsize << " " << gDifferenceNoTrk->Eval(0) << " " << gDifferenceNoTrk->Eval(phantomSize/2) << " " << gDifferenceLPM->Eval(0) << " " << gDifferenceLPM->Eval(phantomSize/2) << " " << gDifferenceKrah->Eval(0) << " " << gDifferenceKrah->Eval(phantomSize/2) << " " << hResEnergy->GetMean() << endl;
      file.close();
   }
   else if (rotation >= 0) {
      ofstream file(Form("Output/MLPerror_energy%.0fMeV_Water_rotation.csv", initialEnergy), ofstream::out | ofstream::app);
      file << phantomSize << " " << rotation << " " <<  gDifferenceNoTrk->Eval(0) << " " << gDifferenceNoTrk->Eval(phantomSize/2) << " " << gDifferenceLPM->Eval(0) << " " << gDifferenceLPM->Eval(phantomSize/2) << " " << sigmaNoTrk << " " << sigmaLPM << endl;
      file.close();
   }
   else {
      ofstream file(Form("Output/MLPerror_energy%.0fMeV_Water_krah.csv", initialEnergy), ofstream::out | ofstream::app);
      file << phantomSize << " " <<  gDifferenceNoTrk->Eval(0) << " " << gDifferenceNoTrk->Eval(phantomSize/2) << " " << gDifferenceLPM->Eval(0) << " " << gDifferenceLPM->Eval(phantomSize/2) << " " << gDifferenceKrah->Eval(0) << " " << gDifferenceKrah->Eval(phantomSize/2) << " " << hResEnergy->GetMean() << " " << 1.0 << endl; // last value is a dummy... 
      file.close();
   }

}


float Sigmat1(float position)
{
	float p = position;
	float sigt1 = (azero*p)+(aone*p*p/2)+(atwo*p*p*p/3)+(athree*p*p*p*p/4)+(afour*p*p*p*p*p/5)+(afive*p*p*p*p*p*p/6);
	
	return (13.6*13.6*pow((1+0.038*log(position/X_0)),2)*sigt1/X_0);
}

float Sigmaz1(float position)
{
	float p = position;
	float sigz1 = (azero*p*p*p/3)+(aone*p*p*p*p/12)+(atwo*p*p*p*p*p/30)+(athree*p*p*p*p*p*p/60)+(afour*p*p*p*p*p*p*p/105)+(afive*p*p*p*p*p*p*p*p/168);
	
	return (13.6*13.6*pow((1+0.038*log(position/X_0)),2)*sigz1/X_0);
}

float Sigmatz1(float position)
{
	float p = position;
	float sigtz1 = (azero*p*p/2)+(aone*p*p*p/6)+(atwo*p*p*p*p/12)+(athree*p*p*p*p*p/20)+(afour*p*p*p*p*p*p/30)+(afive*p*p*p*p*p*p*p/42);
	
	return (13.6*13.6*pow((1+0.038*log(position/X_0)),2)*sigtz1/X_0);
}

float Sigmat2(float sep, float position)
{
	float p = position;
	float s = sep;
	float sigt2 = ((azero*s)+(aone*s*s/2)+(atwo*s*s*s/3)+(athree*s*s*s*s/4)+(afour*s*s*s*s*s/5)+(afive*s*s*s*s*s*s/6))-((azero*p)+(aone*p*p/2)+(atwo*p*p*p/3)+(athree*p*p*p*p/4)+(afour*p*p*p*p*p/5)+(afive*p*p*p*p*p*p/6));
	
	return (13.6*13.6*pow((1+0.038*log((sep-position)/X_0)),2)*sigt2/X_0);
}

float Sigmaz2(float sep, float position)
{
	float p = position;
	float s = sep;
	float sigz2 = (azero*s*s*s/3)+(aone*s*s*s*s/12)+(atwo*s*s*s*s*s/30)+(athree*s*s*s*s*s*s/60)+(afour*s*s*s*s*s*s*s/105)+(afive*s*s*s*s*s*s*s*s/168)-((azero*s*s*p)+(((aone*s*s/2)-(azero*s))*p*p)+(((atwo*s*s/3)-(2*aone*s/3)+(azero/3))*p*p*p)+(((athree*s*s/4)-(atwo*s/2)+(aone/4))*p*p*p*p)+(((afour*s*s/5)-(2*athree*s/5)+(atwo/5))*p*p*p*p*p)+(((afive*s*s/6)-(afour*s/3)+(athree/6))*p*p*p*p*p*p)+(((afour/7)-(2*afive*s/7))*p*p*p*p*p*p*p)+(afive*p*p*p*p*p*p*p*p/8));
	
	return (13.6*13.6*pow((1+0.038*log((sep-position)/X_0)),2)*sigz2/X_0);
}

float Sigmatz2(float sep, float position)
{
	float p = position;
	float s = sep;
	float sigtz2 = ((azero*s*s/2)+(aone*s*s*s/6)+(atwo*s*s*s*s/12)+(athree*s*s*s*s*s/20)+(afour*s*s*s*s*s*s/30)+(afive*s*s*s*s*s*s*s/42))-((azero*s*p)+(((aone*s)-azero)*p*p/2)+(((atwo*s)-aone)*p*p*p/3)+(((athree*s)-atwo)*p*p*p*p/4)+(((afour*s)-athree)*p*p*p*p*p/5)+(((afive*s)-afour)*p*p*p*p*p*p/6)-(afive*p*p*p*p*p*p*p/7));
	
	return (13.6*13.6*pow((1+0.038*log((sep-position)/X_0)),2)*sigtz2/X_0);
}
