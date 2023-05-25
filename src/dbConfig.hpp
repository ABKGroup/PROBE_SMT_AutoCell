#pragma once
#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <vector>

class dbConfig {
  /*
    Configuration for Design Rule, Flow Constraints, Constraint Simplification
    and Graph Settings.
  */
public:
  dbConfig(const std::string &config_path);
  // not used
  dbConfig();

  // fixed parameters for EUV-Tight or EUV-Loose
  dbConfig(const std::string &config_path, std::string infile);

  dbConfig(int BoundaryCondition, int SON, int DoublePowerRail,
           int MM_Parameter, int EXT_Parameter, int BCP_Parameter,
           int MAR_Parameter, int EOL_Parameter, float VR_Parameter,
           int PRL_Parameter, int SHR_Parameter, int MPL_Parameter,
           int XOL_Mode, int NDE_Parameter, int Partition_Parameter,
           int ML_Parameter, int Local_Parameter, int tolerance_Parameter,
           int BS_Parameter, int objpart_Parameter, int XOL_Parameter);

  void checkParameter();

  void setDR_Parameter(std::string DR_Parameter) {
    DR_Parameter_ = DR_Parameter;
  }

  void setBoundaryCondition(int BoundaryCondition) {
    BoundaryCondition_ = BoundaryCondition;
  }

  void setSON(int SON) { SON_ = SON; }

  void setDoublePowerRail(int DoublePowerRail) {
    DoublePowerRail_ = DoublePowerRail;
  }

  void setMM_Parameter(int MM_Parameter) { MM_Parameter_ = MM_Parameter; }

  void setEXT_Parameter(int EXT_Parameter) { EXT_Parameter_ = EXT_Parameter; }

  void setBCP_Parameter(int BCP_Parameter) { BCP_Parameter_ = BCP_Parameter; }

  void setMAR_Parameter(int MAR_Parameter) { MAR_Parameter_ = MAR_Parameter; }

  void setEOL_Parameter(int EOL_Parameter) { EOL_Parameter_ = EOL_Parameter; }

  void setVR_Parameter(float VR_Parameter) { VR_Parameter_ = VR_Parameter; }

  void setPRL_Parameter(int PRL_Parameter) { PRL_Parameter_ = PRL_Parameter; }

  void setSHR_Parameter(int SHR_Parameter) { SHR_Parameter_ = SHR_Parameter; }

  void setMPL_Parameter(int MPL_Parameter) { MPL_Parameter_ = MPL_Parameter; }

  void setXOL_Mode(int XOL_Mode) {
    XOL_Mode_ = XOL_Mode;
    if (XOL_Mode == 0) {
      XOL_Parameter_ = 2;
    } else {
      XOL_Parameter_ = 4;
    }
  }

  void setNDE_Parameter(int NDE_Parameter) { NDE_Parameter_ = NDE_Parameter; }

  void setPartition_Parameter(int Partition_Parameter) {
    Partition_Parameter_ = Partition_Parameter;
  }

  void setML_Parameter(int ML_Parameter) { ML_Parameter_ = ML_Parameter; }

  void setLocal_Parameter(int Local_Parameter) {
    Local_Parameter_ = Local_Parameter;
  }

  void setTolerance_Parameter(int tolerance_Parameter) {
    tolerance_Parameter_ = tolerance_Parameter;
  }

  void setBS_Parameter(int BS_Parameter) { BS_Parameter_ = BS_Parameter; }

  void setObjpart_Parameter(int objpart_Parameter) {
    objpart_Parameter_ = objpart_Parameter;
  }

  void setXOL_Parameter(int XOL_Parameter) { XOL_Parameter_ = XOL_Parameter; }

  std::string getDR_Parameter() {
    return DR_Parameter_;
  }

  int getBoundaryCondition() { return BoundaryCondition_; }

  int getSON() { return SON_; }

  int getDoublePowerRail() { return DoublePowerRail_; }

  int getMM_Parameter() { return MM_Parameter_; }

  int getEXT_Parameter() { return EXT_Parameter_; }

  int getBCP_Parameter() { return BCP_Parameter_; }

  int getMAR_Parameter() { return MAR_Parameter_; }

  int getEOL_Parameter() { return EOL_Parameter_; }

  float getVR_Parameter() { return VR_Parameter_; }

  int getPRL_Parameter() { return PRL_Parameter_; }

  int getSHR_Parameter() { return SHR_Parameter_; }

  int getMPL_Parameter() { return MPL_Parameter_; }

  int getXOL_Mode() { return XOL_Mode_; }

  int getNDE_Parameter() { return NDE_Parameter_; }

  int getPartition_Parameter() { return Partition_Parameter_; }

  int getML_Parameter() { return ML_Parameter_; }

  int getLocal_Parameter() { return Local_Parameter_; }

  int getTolerance_Parameter() { return tolerance_Parameter_; }

  int getBS_Parameter() { return BS_Parameter_; }

  int getObjpart_Parameter() { return objpart_Parameter_; }

  int getXOL_Parameter() { return XOL_Parameter_; }

private:
  // User defined Design Parameteres
  std::string DR_Parameter_;
  // 0: Fixed, 1: Extensible
  int BoundaryCondition_;
  // 0: Disable, 1: Enable
  int SON_;
  // 0: Disable, 1: Enable
  int DoublePowerRail_;
  // 3: Maximum Number of MetalLayer
  int MM_Parameter_;
  // 0 only
  int EXT_Parameter_;
  // 0: Disable 1: Enable BCP(Default)
  int BCP_Parameter_;
  // ARGV[1], Minimum Area 1: (Default), Integer
  int MAR_Parameter_;
  // ARGV[2], End-of-Line  1: (Default), Integer
  int EOL_Parameter_;
  // ARGV[3], VIA sqrt(2)=1.5 : (Default), Floating
  float VR_Parameter_;
  // ARGV[4], Parallel Run-length 1: (Default). Integer
  int PRL_Parameter_;
  // ARGV[5], Step Heights 1: (Default), Integer
  int SHR_Parameter_;
  // ARGV[6], 3: (Default) Minimum Pin Opening
  int MPL_Parameter_;
  // ARGV[7], 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  int XOL_Mode_;
  // ARGV[8], 0: Disable(Default) 1: Enable NDE
  int NDE_Parameter_;
  // ARGV[9], 0: Disable(Default) 1. Cell Partitioning
  int Partition_Parameter_;
  // ARGV[10], 5: (Default) Min Metal Length for avoiding adjacent signal
  // routing (only works with special net setting)
  int ML_Parameter_;
  // ARGV[11], 0: Disable(Default) 1: Localization for
  // Internal node within same diffusion region
  int Local_Parameter_;
  // ARGV[12], Localization Offset Margin, Integer
  int tolerance_Parameter_;
  // ARGV[13], 0: Disable(Default) 1: Enable BS(Breaking Symmetry)
  int BS_Parameter_;
  // ARGV[14], 0: Disable(Default) 1. Objective Partitioning
  int objpart_Parameter_;
  // Depends on XOL_Mode
  int XOL_Parameter_;
};