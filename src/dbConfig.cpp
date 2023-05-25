#define FMT_HEADER_ONLY
#include "dbConfig.hpp"
#include <fmt/core.h>
#include <fmt/format.h>

dbConfig::dbConfig(const std::string &config_path) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();

  // parse into variables
  BoundaryCondition_ = config["BoundaryCondition"]["value"];
  SON_ = config["SON"]["value"];
  DoublePowerRail_ = config["DoublePowerRail"]["value"];
  MM_Parameter_ = config["MM_Parameter"]["value"];
  EXT_Parameter_ = config["EXT_Parameter"]["value"];
  BCP_Parameter_ = config["BCP_Parameter"]["value"];
  MAR_Parameter_ = config["MAR_Parameter"]["value"];
  EOL_Parameter_ = config["EOL_Parameter"]["value"];
  VR_Parameter_ = config["VR_Parameter"]["value"];
  PRL_Parameter_ = config["PRL_Parameter"]["value"];
  SHR_Parameter_ = config["SHR_Parameter"]["value"];
  MPL_Parameter_ = config["MPL_Parameter"]["value"];
  XOL_Mode_ = config["XOL_Mode"]["value"];
  NDE_Parameter_ = config["NDE_Parameter"]["value"];
  Partition_Parameter_ = config["Partition_Parameter"]["value"];
  ML_Parameter_ = config["ML_Parameter"]["value"];
  Local_Parameter_ = config["Local_Parameter"]["value"];
  tolerance_Parameter_ = config["tolerance_Parameter"]["value"];
  BS_Parameter_ = config["BS_Parameter"]["value"];
  objpart_Parameter_ = config["objpart_Parameter"]["value"];
  XOL_Parameter_ = config["XOL_Parameter"]["value"];

  dbConfig::checkParameter();
}

dbConfig::dbConfig() {
  // User defined Design Parameteres
  // 0: Fixed, 1: Extensible
  BoundaryCondition_ = 0;
  // 0: Disable, 1: Enable
  SON_ = 1;
  // 0: Disable, 1: Enable
  DoublePowerRail_ = 0;
  // 3: Maximum Number of MetalLayer
  MM_Parameter_ = 4;
  // 0 only
  EXT_Parameter_ = 0;
  // 0: Disable 1: Enable BCP(Default)
  BCP_Parameter_ = 1;
  // ARGV[1], Minimum Area 1: (Default), Integer
  MAR_Parameter_ = 1;
  // ARGV[2], End-of-Line  1: (Default), Integer
  EOL_Parameter_ = 1;
  // ARGV[3], VIA sqrt(2)=1.5 : (Default), Floating
  VR_Parameter_ = 1.5;
  // ARGV[4], Parallel Run-length 1: (Default). Integer
  PRL_Parameter_ = 1;
  // ARGV[5], Step Heights 1: (Default), Integer
  SHR_Parameter_ = 1;
  // ARGV[6], 3: (Default) Minimum Pin Opening
  MPL_Parameter_ = 3;
  // ARGV[7], 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  XOL_Mode_ = 2;
  // ARGV[8], 0: Disable(Default) 1: Enable NDE
  NDE_Parameter_ = 0;
  // ARGV[9], 0: Disable(Default) 1. Cell Partitioning
  Partition_Parameter_ = 0;
  // ARGV[10], 5: (Default) Min Metal Length for avoiding adjacent signal
  // routing (only works with special net setting)
  ML_Parameter_ = 5;
  // ARGV[11], 0: Disable(Default) 1: Localization for
  // Internal node within same diffusion region
  Local_Parameter_ = 0;
  // ARGV[12], Localization Offset Margin, Integer
  tolerance_Parameter_ = 1;
  // ARGV[13], 0: Disable(Default) 1: Enable BS(Breaking Symmetry)
  BS_Parameter_ = 0;
  // ARGV[14], 0: Disable(Default) 1. Objective Partitioning
  objpart_Parameter_ = 0;
  // Depends on XOL_Mode
  XOL_Parameter_ = 2;
  dbConfig::checkParameter();
}

dbConfig::dbConfig(const std::string &config_path, std::string infile) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();

  XOL_Parameter_ = config["XOL_Parameter"]["value"];
  MPL_Parameter_ = config["MPL_Parameter"]["value"];
  EXT_Parameter_ = config["EXT_Parameter"]["value"];
  DR_Parameter_ = config["DRTYPE_Parameter"]["value"];
  tolerance_Parameter_ = config["tolerance_Parameter"]["value"];
  // EUV-Loose
  if (DR_Parameter_ == "EL") {
    BoundaryCondition_ = 0;
    SON_ = 1;
    DoublePowerRail_ = 0;
    MAR_Parameter_ = 1;
    EOL_Parameter_ = 1;
    VR_Parameter_ = 1.0;
    PRL_Parameter_ = 0;
    SHR_Parameter_ = 0;
    MM_Parameter_ = 4;
    Local_Parameter_ = 1;
    Partition_Parameter_ = 0;
    BCP_Parameter_ = 1;
    NDE_Parameter_ = 0;
    BS_Parameter_ = 1;
  } else if (DR_Parameter_ == "ET") {
    // EUV-Tight
    BoundaryCondition_ = 0;
    SON_ = 1;
    DoublePowerRail_ = 0;
    MAR_Parameter_ = 1;
    EOL_Parameter_ = 2;
    VR_Parameter_ = 1.0;
    PRL_Parameter_ = 0;
    SHR_Parameter_ = 0;
    MM_Parameter_ = 4;
    Local_Parameter_ = 1;
    Partition_Parameter_ = 0;
    BCP_Parameter_ = 1;
    NDE_Parameter_ = 0;
    BS_Parameter_ = 1;
  } else {
    fmt::print("[ERROR] DesignRule Type is not valid!\n");
    exit(-1);
  }

  if (MPL_Parameter_ < 2 || MPL_Parameter_ > 4) {
    fmt::print("[ERROR] MPL_Parameter_ is not valid!\n");
    exit(-1);
  }

  // Special Condition for DFF cells
  if (infile.find("DFF") != std::string::npos) {
    Partition_Parameter_ = 2;
    BCP_Parameter_ = 1;
    NDE_Parameter_ = 0;
    BS_Parameter_ = 0;
  }
}

dbConfig::dbConfig(int BoundaryCondition, int SON, int DoublePowerRail,
                   int MM_Parameter, int EXT_Parameter, int BCP_Parameter,
                   int MAR_Parameter, int EOL_Parameter, float VR_Parameter,
                   int PRL_Parameter, int SHR_Parameter, int MPL_Parameter,
                   int XOL_Mode, int NDE_Parameter, int Partition_Parameter,
                   int ML_Parameter, int Local_Parameter,
                   int tolerance_Parameter, int BS_Parameter,
                   int objpart_Parameter, int XOL_Parameter) {
  BoundaryCondition_ = BoundaryCondition;
  SON_ = SON;
  DoublePowerRail_ = DoublePowerRail;
  MM_Parameter_ = MM_Parameter;
  EXT_Parameter_ = EXT_Parameter;
  BCP_Parameter_ = BCP_Parameter;
  MAR_Parameter_ = MAR_Parameter;
  EOL_Parameter_ = EOL_Parameter;
  VR_Parameter_ = VR_Parameter;
  PRL_Parameter_ = PRL_Parameter;
  SHR_Parameter_ = SHR_Parameter;
  MPL_Parameter_ = MPL_Parameter;
  XOL_Mode_ = XOL_Mode;
  NDE_Parameter_ = NDE_Parameter;
  Partition_Parameter_ = Partition_Parameter;
  ML_Parameter_ = ML_Parameter;
  Local_Parameter_ = Local_Parameter;
  tolerance_Parameter_ = tolerance_Parameter;
  BS_Parameter_ = BS_Parameter;
  objpart_Parameter_ = objpart_Parameter;
  XOL_Parameter_ = XOL_Parameter;
  dbConfig::checkParameter();
}

void dbConfig::checkParameter() {
  if (MAR_Parameter_ == 0) {
    std::cout << "\n*** Disable MAR (When Parameter == 0) ***\n";
  }
  if (EOL_Parameter_ == 0) {
    std::cout << "\n*** Disable EOL (When Parameter == 0) ***\n";
  }
  if (VR_Parameter_ == 0) {
    std::cout << "\n*** Disable VR (When Parameter == 0) ***\n";
  }
  if (PRL_Parameter_ == 0) {
    std::cout << "\n*** Disable PRL (When Parameter == 0) ***\n";
  }
  if (SHR_Parameter_ < 2) {
    std::cout << "\n*** Disable SHR (When Parameter <= 1) ***\n";
  }
  if (Local_Parameter_ == 0) {
    std::cout << "\n*** Disable Localization (When Parameter == 0) ***\n";
  }
  if (Partition_Parameter_ == 0) {
    std::cout << "\n*** Disable Cell Partitioning (When Parameter == 0) ***\n";
  }
  if (objpart_Parameter_ == 0) {
    std::cout
        << "\n*** Disable Objective Partitioning (When Parameter == 0) ***\n";
  }
  if (BS_Parameter_ == 0) {
    std::cout << "\n*** Disable Breaking Symmetry (When Parameter == 0) ***\n";
  }
  if (NDE_Parameter_ == 0) {
    std::cout << "\n*** Disable FST (When Parameter == 0) ***\n";
  }

  if (XOL_Mode_ == 0) {
    XOL_Parameter_ = 2;
  } else {
    XOL_Parameter_ = 4;
  }
}
