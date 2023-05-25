#define FMT_HEADER_ONLY
#include <algorithm>
#include <boost/algorithm/string/classification.hpp> // Include boost::for is_any_of
#include <boost/algorithm/string/split.hpp>          // Include for boost::split
#include <boost/multiprecision/integer.hpp>          // for returning bit length
#include <cmath>
#include <filesystem>
#include <fmt/core.h>
#include <fmt/format.h>
#include <fstream>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

#include "genSMTInput.hpp"
namespace bmp = boost::multiprecision;

// Example: ./genSMTInput ./pinLayouts/BUFx4.pinLayout ./config/config.json

int main(int argc, char *argv[]) {
  // ### Pre-processing ########################################################
  auto const workdir = std::filesystem::current_path();
  auto const outdir = workdir / "inputsSMT";
  std::string pinlayout_path = "";
  std::string config_path = "";

  dbConfig *config;
  SMTCell *SMTCell;
  // SMTCell->init();

  if (argc != 3) {
    std::cerr << "\n*** Error:: Wrong CMD";
    std::cerr << "\n   [USAGE]: ./PL_FILE [inputfile_pinLayout] "
                 "[inputfile_config]\n\n";
    exit(1);
  } else {
    pinlayout_path = argv[1];
    config_path = argv[2];
  }

  // check input files
  std::ifstream config_file(config_path);
  std::ifstream pinlayout_file(pinlayout_path);

  if (!config_file.good()) {
    fmt::print("\n*** Error:: FILE DOES NOT EXIST..{}\n", config_path);
    exit(-1);
  } else {
    // Read Gear Ratio Configuration
    config = new dbConfig(config_path, pinlayout_path);
    SMTCell->initTrackInfo(config_path);
  }

  if (!pinlayout_file.good()) {
    fmt::print("\n*** Error:: FILE DOES NOT EXIST..{}\n", pinlayout_path);
    exit(-1);
  } else {
    fmt::print("\n");
    fmt::print("a   Version Info : 1.0 Initial Release\n");
    fmt::print("a        Design Rule Parameters : [MAR = {}, EOL = {}, VR = "
               "{}, PRL = {}, SHR = {}]\n",
               config->getMAR_Parameter(), config->getEOL_Parameter(),
               config->getVR_Parameter(), config->getPRL_Parameter(),
               config->getSHR_Parameter());
    fmt::print(
        "a        Parameter Options : [MPO = {}], [Localization = {} (T{})]\n",
        config->getMPL_Parameter(), config->getLocal_Parameter(),
        config->getTolerance_Parameter());
    fmt::print("a	                        [Cell Partitioning = {}], [FST "
               "= {}], [Breaking Symmetry = {}]\n",
               config->getPartition_Parameter(),
               (config->getNDE_Parameter() == 0 ? "Disable" : "Enable"),
               config->getBS_Parameter());
    fmt::print("a	                        [DBMode = {}({})], [Objective "
               "Partitioning = {}]\n\n",
               config->getXOL_Mode(), config->getXOL_Parameter(),
               config->getObjpart_Parameter());

    fmt::print("a   Generating SMT-LIB 2.0 Standard inputfile based on the "
               "following files.\n");
    fmt::print("a     Input Layout:  {}/{}\n", workdir.c_str(), pinlayout_path);
  }

  // ### Output Directory Creation, please see the following reference:
  system(("mkdir -p " + outdir.string()).c_str());
  auto tmp = pinlayout_path.substr(pinlayout_path.rfind("/") + 1);
  auto outfile =
      outdir /
      tmp.substr(0, tmp.find("."))
          .append(fmt::format("_{}F_{}T_{}_MPO{}.smt2", SMTCell->getNumFin(),
                              SMTCell->getNumTrack(), config->getDR_Parameter(),
                              config->getMPL_Parameter()));
  fmt::print("a     SMT-LIB2.0 File:    {}\n", outfile.c_str());
  tmp.clear();

  SMTCell->setNumMetalLayer(config->getMM_Parameter()); // M1~M4

  // Perl if not able to fetch a val from map, it will use None
  // Instance *tmp_inst;

  // parse pinlayout file
  LayoutParser *parser = new LayoutParser();
  parser->parsePinLayout(pinlayout_path, config->getPartition_Parameter());

  Placement *plc = new Placement();
  plc->init_InstPartition(config->getPartition_Parameter());
  // SMTCell->dump_InstPartitionPMOS();
  // SMTCell->dump_InstPartitionNMOS();

  // ### Remove Power Pin/Net Information from data structure
  // Remove Power Pin
  SMTCell->removePowerPin();

  // Remove Power Net
  SMTCell->removePowerNet();

  fmt::print("a     # Pins              = {}\n", SMTCell->getPinCnt());
  fmt::print("a     # Nets              = {}\n", SMTCell->getNetCnt());

  Graph *graph = new Graph();

  // ### VERTEX Generation
  graph->init_vertices();
  // SMTCell->dump_vertices();
  fmt::print("a     # Vertices          = {}\n", SMTCell->getVertexCnt());
  // exit(0);

  // ### UNDIRECTED EDGE Generation
  graph->init_udedges();
  // SMTCell->dump_udEdges();
  // exit(0);
  // bug fixed: minus undef edges
  fmt::print("a     # udEdges           = {}\n", SMTCell->getUdEdgeCnt());

  // ### BOUNDARY VERTICES Generation.
  int numBoundaries = 0;
  graph->init_boundaryVertices(config->getEXT_Parameter());
  fmt::print("a     # Boundary Vertices = {}\n",
             SMTCell->getBoundaryVertexCnt());

  graph->init_outerPins();
  fmt::print("a     # Outer Pins        = {}\n", SMTCell->getOuterPinCnt());

  graph->init_corner();
  fmt::print("a     # Left Corners      = {}\n", SMTCell->getLeftCornerCnt());
  fmt::print("a     # Right Corners     = {}\n", SMTCell->getRightCornerCnt());
  fmt::print("a     # Front Corners     = {}\n", SMTCell->getFrontCornerCnt());
  fmt::print("a     # Back Corners      = {}\n", SMTCell->getBackCornerCnt());

  // ### SOURCE and SINK Generation. All
  // sources and sinks are supernodes.
  // ### DATA STRUCTURE:  SOURCE or SINK
  // [netName] [#subNodes] [Arr. of
  // sub-nodes, i.e., vertices]
  // Super Outer Node Keyword
  std::string keySON = "pinSON";
  graph->init_source(config->getSON());

  fmt::print("a     # Ext Nets          = {}\n", SMTCell->getExtNetCnt());
  fmt::print("a     # Sources           = {}\n", SMTCell->getSourceCnt());
  fmt::print("a     # Sinks             = {}\n", SMTCell->getSinkCnt());
  graph->init_pinSON(config->getSON());

  // ### VIRTUAL EDGE Generation
  // ### We only define directed virtual edges since we know the direction based
  // on source/sink information.
  // ### All supernodes are having names starting with 'pin'.
  // ### DATA STRUCTURE:  VIRTUAL_EDGE [index] [Origin] [Destination] [Cost=0]
  graph->init_virtualEdges();
  graph->init_edgeInOut();
  graph->init_vedgeInOut();

  fmt::print("a     # Virtual Edges     = {}\n", SMTCell->getVirtualEdgeCnt());
  // ### END:  DATA STRUCTURE
  // ###########################################################################

  std::FILE *out = std::fopen(outfile.c_str(), "w");
  fmt::print("a   Generating SMT-LIB 2.0 Standard Input Code.\n");

  // INIT
  fmt::print(out, ";Formulation for SMT\n");
  fmt::print(out, "; Format: SMT-LIB 2.0\n");
  fmt::print(out, "; Version: 1.0\n");
  fmt::print(out, "; Authors: Daeyeal Lee, Dongwon Park, Chung-Kuan Cheng\n");
  fmt::print(out, "; DO NOT DISTRIBUTE IN ANY PURPOSE!\n\n");
  fmt::print(out, "; Input File:  {}/{}\n", workdir.c_str(), pinlayout_path);
  fmt::print(out,
             "; Design Rule Parameters : [MAR = {}, EOL = {}, VR = {}, PRL = "
             "{}, SHR = {}]\n",
             config->getMAR_Parameter(), config->getEOL_Parameter(),
             config->getVR_Parameter(), config->getPRL_Parameter(),
             config->getSHR_Parameter());
  fmt::print(out,
             "; Parameter Options : [MPO = {}], [Localization = {} (T{})]\n",
             config->getMPL_Parameter(), config->getLocal_Parameter(),
             config->getTolerance_Parameter());
  fmt::print(
      out, "; [Cell Partitioning = {}], [FST = {}], [Breaking Symmetry = {}]\n",
      config->getPartition_Parameter(),
      (config->getNDE_Parameter() == 0 ? "Disable" : "Enable"),
      config->getBS_Parameter());
  fmt::print(out, "; [DBMode = {}({})], [Objective Partitioning = {}]\n\n",
             config->getXOL_Mode(), config->getXOL_Parameter(),
             config->getObjpart_Parameter());

  fmt::print(out, ";Layout Information\n");
  fmt::print(out, ";	Placement\n");
  // fmt::print(out, ";	# Vertical Tracks   = {}\n", SMTCell->getNumPTrackV());
  fmt::print(out, ";	# Vertical Tracks   = {}\n",
             SMTCell->getRealNumPTrackV());
  fmt::print(out, ";	# Horizontal Tracks = {}\n", SMTCell->getNumPTrackH());
  fmt::print(out, ";	# Instances         = {}\n", SMTCell->getNumInstance());
  fmt::print(out, ";	Routing\n");
  // fmt::print(out, ";	# Vertical Tracks   = {}\n", SMTCell->getNumTrackV());
  fmt::print(out, ";	# Vertical Tracks   = {}\n",
             SMTCell->getRealNumTrackV());
  fmt::print(out, ";	# Horizontal Tracks = {}\n", SMTCell->getNumTrackH());
  fmt::print(out, ";	# Nets              = {}\n", SMTCell->getNetCnt());
  fmt::print(out, ";	# Pins              = {}\n", SMTCell->getPinCnt());
  fmt::print(out, ";	# Sources           = {}\n", SMTCell->getSourceCnt());
  fmt::print(out, ";	List of Sources   = ");

  fmt::print(out, "{}", SMTCell->dump_sources());
  fmt::print(out, "\n");
  fmt::print(out, ";	# Sinks             = {}\n", SMTCell->getSinkCnt());
  fmt::print(out, ";	List of Sinks     = ");

  fmt::print(out, "{}", SMTCell->dump_sinks());
  fmt::print(out, "\n");
  fmt::print(out, ";	# Outer Pins        = {}\n", SMTCell->getOuterPinCnt());
  fmt::print(out, ";	List of Outer Pins= ");

  // All SON (Super Outer Node)
  fmt::print(out, "{}", SMTCell->dump_SON());
  fmt::print(out, "\n");
  fmt::print(out, ";	Outer Pins Information= ");

  // All SON (Super Outer Node)
  fmt::print(out, "{}", SMTCell->dump_SON_detail());
  fmt::print(out, "\n");
  fmt::print(out, "\n\n");

  // ### Z3 Option Set ###
  // Flow related constraints will be handled by Flow Writer
  fmt::print(out, ";Begin SMT Formulation\n\n");
  FlowWriter *flowWriter = new FlowWriter();
  DesignRuleWriter *drWriter = new DesignRuleWriter();
  plc->init_cost_var(out);

  // ### Placement ###
  fmt::print("a   A. Variables for Placement\n");
  fmt::print(out, ";A. Variables for Placement\n");

  plc->write_max_func(out);
  plc->write_placement_var(out);

  fmt::print("a   B. Constraints for Placement\n");
  fmt::print(out, "\n");
  fmt::print(out, ";B. Constraints for Placement\n");

  plc->write_placement_range_constr(out);

  // PMOS Area
  plc->set_placement_var_pmos(out);

  // NMOS Area
  plc->set_placement_var_nmos(out);

  // Force Gate to be placed on even columns, S/D otherwise
  // With Gear Ratio, you want to set on even multiples of the M1 pitch
  plc->write_bin_grid_constr(out);

  SMTCell->setMOSMinWidth();

  plc->remove_symmetric_placement(out, config->getBS_Parameter());

  std::vector<int> g_p_h1;
  std::vector<int> g_p_h2;
  std::vector<int> g_p_h3;
  std::vector<int> g_n_h1;
  std::vector<int> g_n_h2;
  std::vector<int> g_n_h3;
  int w_p_h1 = 0;
  int w_p_h2 = 0;
  int w_p_h3 = 0;
  int w_n_h1 = 0;
  int w_n_h2 = 0;
  int w_n_h3 = 0;
  std::map<int, int> h_g_inst;

  // fmt::print("XOL Mode = {}\n", config->getXOL_Mode());
  // XOL Mode => 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  plc->write_XOL(out, true, config->getXOL_Parameter(), config->getNDE_Parameter(),
                 config->getXOL_Parameter());
  plc->write_XOL(out, false, config->getXOL_Parameter(), config->getNDE_Parameter(),
                 config->getXOL_Parameter());

  fmt::print(out, "\n");

  // ### Routing ###
  // fmt::print(out, "a   C. Variables for Routing\n");

  // fmt::print(out, "a   D. Constraints for Routing\n");
  // ### SOURCE and SINK DEFINITION per NET per COMMODITY and per VERTEX
  // (including supernodes, i.e., pins)
  // ### Preventing from routing Source/Drain Node using M1 Layer. Only Gate
  // Node can use M1 between PMOS/NMOS Region
  // ### UNDIRECTED_EDGE [index] [Term1] [Term2] [Cost]
  // #";Source/Drain Node between PMOS/NMOS region can not connect using M1
  // Layer.\n\n";

  if (SMTCell::DEBUG)
    fmt::print("1. cnt: {}\n", SMTCell::getAssignedCnt());

  graph->init_metal_var();
  graph->init_net_edge_var();
  graph->init_net_commodity_edge_var();

  if (SMTCell::DEBUG)
    fmt::print("2. cnt: {}\n", SMTCell::getAssignedCnt());

  // ### Extensible Boundary variables
  // # In Extensible Case , Metal binary variables
  graph->init_extensible_boundary(config->getBoundaryCondition());

  if (SMTCell::DEBUG)
    fmt::print("3. cnt: {}\n", SMTCell::getAssignedCnt());

  // ### Commodity Flow binary variables
  flowWriter->init_commodity_flow_var();

  if (SMTCell::DEBUG)
    fmt::print("4. cnt: {}\n", SMTCell::getAssignedCnt());

  plc->localize_adjacent_pin(config->getLocal_Parameter());

  // fmt::print("5. cnt: {}\n", SMTCell::getAssignedCnt());
  int isEnd = 0;
  int numLoop = 0;

  while (isEnd == 0) {
    if (SMTCell::DEBUG)
      fmt::print("***start. cnt: {}\n", SMTCell::getAssignedCnt());
    if (SMTCell::DEBUG)
      fmt::print("      *** 1. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    if (SMTCell->getCandidateAssignCnt() > 0) {
      // ## Merge Assignment Information
      SMTCell->mergeAssignment();
    }

    if (numLoop == 0) {
      fmt::print("a    Initial SMT Code Generation\n");
    } else {
      fmt::print("a    SMT Code Reduction Loop #{}\n", numLoop);
    }

    SMTCell->reset_var();
    SMTCell->reset_cnt();

    // ### Set Default Gate Metal according to the capacity variables
    // std::map<const std::string, int> h_tmp;
    plc->set_default_G_metal();
    plc->unset_rightmost_metal();

    // crosstalk mitigation by special net constraint
    plc->write_special_net_constraint(config->getML_Parameter());

    // device partition constraint
    plc->write_partition_constraint(config->getPartition_Parameter());

    plc->init_placement_G_pin();

    plc->init_placement_overlap_SD_pin();

    if (SMTCell::DEBUG)
      fmt::print("      *** 2. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    SMTCell->writeConstraint(";Flow Capacity Control\n");
    flowWriter->write_flow_capacity_control();

    if (SMTCell::DEBUG)
      fmt::print("      *** 3. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    flowWriter->localize_commodity(config->getLocal_Parameter(),
                                   config->getTolerance_Parameter());

    if (SMTCell::DEBUG)
      fmt::print("      *** 4. new cnt: {}\n", SMTCell::getNewAssignedCnt());
    // ### COMMODITY FLOW Conservation
    fmt::print("a     1. Commodity flow conservation ");
    flowWriter->write_flow_conservation(out, config->getEXT_Parameter());

    if (SMTCell::DEBUG)
      fmt::print("      *** 5. new cnt: {}\n", SMTCell::getNewAssignedCnt());
    // ### Exclusiveness use of VERTEX.  (Only considers incoming flows by
    // nature.)

    fmt::print("a     2. Exclusiveness use of vertex ");
    flowWriter->write_vertex_exclusive(out);

    if (SMTCell::DEBUG)
      fmt::print("      *** 6. new cnt: {}\n", SMTCell::getNewAssignedCnt());
    
    // ### EDGE assignment  (Assign edges based on commodity information.)
    fmt::print("a     3. Edge assignment ");
    flowWriter->write_edge_assignment(out);

    if (SMTCell::DEBUG)
      fmt::print("      *** 7. new cnt: {}\n", SMTCell::getNewAssignedCnt());
    
    // ### Exclusiveness use of EDGES + Metal segment assignment by using edge
    // usage information
    fmt::print("a     4. Exclusiveness use of edge ");
    flowWriter->write_edge_exclusive(out);

    if (SMTCell::DEBUG)
      fmt::print("      *** 8. new cnt: {}\n", SMTCell::getNewAssignedCnt());
    
    // ### Geometry variables for LEFT, RIGHT, FRONT, BACK directions
    fmt::print("a     6. Geometric variables ");
    drWriter->write_geometric_variables();

    if (SMTCell::DEBUG)
      fmt::print("      *** 9. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    
    fmt::print("a     7. Minimum area rule ");
    drWriter->write_MAR_rule(config->getMAR_Parameter(),
                             config->getDoublePowerRail());

    if (SMTCell::DEBUG)
      fmt::print("      *** 10. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    
    fmt::print("a     8. Tip-to-Tip spacing rule ");
    drWriter->write_EOL_rule(config->getEOL_Parameter(),
                             config->getDoublePowerRail());

    if (SMTCell::DEBUG)
      fmt::print("      *** 11. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    fmt::print("a     9. Via-to-via spacing rule ");
    drWriter->write_VR_rule(config->getVR_Parameter(),
                            config->getDoublePowerRail());

    if (SMTCell::DEBUG)
      fmt::print("      *** 12. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    fmt::print("a     10. Parallel Run Length Rule ");
    drWriter->write_PRL_rule(config->getPRL_Parameter(),
                             config->getDoublePowerRail());

    if (SMTCell::DEBUG)
      fmt::print("      *** 13. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    
    fmt::print("a     11. Net Consistency");
    SMTCell->writeConstraint(";11. Net Consistency\n");
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR] # All Net
    // Variables should be connected to flow variable though it is nor a
    // direct connection
    flowWriter->write_net_consistency();

    if (SMTCell::DEBUG)
      fmt::print("      *** 14. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    fmt::print("a     12. Pin Accessibility Rule ");
    SMTCell->writeConstraint(";12. Pin Accessibility Rule\n");
    // ### Pin Accessibility Rule : External Pin Nets(except VDD/VSS) should
    // have at-least $MPL_Parameter true edges for top-Layer or (top-1)
    // layer(with opening)
    drWriter->write_pin_access_rule(config->getMPL_Parameter(),
                                    config->getMAR_Parameter(),
                                    config->getEOL_Parameter());

    if (SMTCell::DEBUG)
      fmt::print("      *** 15. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    // not used
    fmt::print("a     13. Step Height Rule ");
    SMTCell->writeConstraint(";13. Step Height Rule\n");
    drWriter->write_SHR_rule(config->getSHR_Parameter());

    if (SMTCell::DEBUG)
      fmt::print("      *** 16. new cnt: {}\n", SMTCell::getNewAssignedCnt());

    // break; // when done, comment out
    numLoop++;
    if (SMTCell->getCandidateAssignCnt() == 0 ||
        config->getBCP_Parameter() == 0) {
      isEnd = 1;
    } else {
      SMTCell->clear_writeout();
    }
  }

  int total_var = SMTCell->getTotalVar();
  int total_clause = SMTCell->getTotalClause();
  int total_literal = SMTCell->getTotalLiteral();
  fmt::print("a   C. Variables for Routing\n");
  fmt::print(out, ";C. Variables for Routing\n");

  // Writing to everything .SMT2
  SMTCell->flushVarAndConstraint(out, config->getBCP_Parameter());

  fmt::print("a   E. Check SAT & Optimization\n");
  fmt::print(out, ";E. Check SAT & Optimization\n");
  // cost related to P/N
  plc->write_cost_func_mos(out);

  // top metal track usage
  // matched
  plc->write_top_metal_track_usage(out);
  plc->write_cost_func(out, config->getPartition_Parameter());

  fmt::print(out, "(assert (= COST_SIZE (max COST_SIZE_P COST_SIZE_N)))\n");
  fmt::print(out, "(minimize COST_SIZE)\n");

  plc->write_minimize_cost_func(out, config->getPartition_Parameter());
  fmt::print(out, "(check-sat)\n");
  fmt::print(out, "(get-model)\n");
  fmt::print(out, "(get-objectives)\n");
  fmt::print("a   Total # Variables      = {}\n", total_var);
  fmt::print("a   Total # Literals       = {}\n", total_literal);
  fmt::print("a   Total # Clauses        = {}\n", total_clause);
  fmt::print(out, "; Total # Variables      = {}\n", total_var);
  fmt::print(out, "; Total # Literals       = {}\n", total_literal);
  fmt::print(out, "; Total # Clauses        = {}\n", total_clause);

  std::fclose(out);
  SMTCell->dump_summary();
}
