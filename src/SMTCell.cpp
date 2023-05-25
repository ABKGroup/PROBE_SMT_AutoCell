#include "SMTCell.hpp"

std::string SMTCell::writeout = "";

// Debug Mode
bool SMTCell::DEBUG = false;

// Placement vs. Routing Horizontal Track Mapping Array [Placement, Routing]
std::map<int, int> SMTCell::mapTrack = {{0, 5}, {1, 4}, {2, 4},
                                        {3, 1}, {4, 1}, {5, 0}};

// Number of Routing Contact for Each Width of FET
std::map<int, int> SMTCell::numContact = {{1, 2}, {2, 2}, {3, 2}};
std::map<int, int> SMTCell::h_mapTrack = {};
std::map<int, int> SMTCell::h_RTrack = {};
std::map<int, int> SMTCell::h_numCon = {};

// counting vars
int SMTCell::c_v_placement_ = 0;
int SMTCell::c_v_placement_aux_ = 0;
int SMTCell::c_v_routing_ = 0;
int SMTCell::c_v_routing_aux_ = 0;
int SMTCell::c_v_connect_ = 0;
int SMTCell::c_v_connect_aux_ = 0;
int SMTCell::c_v_dr_ = 0;
int SMTCell::c_c_placement_ = 0;
int SMTCell::c_c_routing_ = 0;
int SMTCell::c_c_connect_ = 0;
int SMTCell::c_c_dr_ = 0;
int SMTCell::c_l_placement_ = 0;
int SMTCell::c_l_routing_ = 0;
int SMTCell::c_l_connect_ = 0;
int SMTCell::c_l_dr_ = 0;

// Gear Ratio Info
int SMTCell::metalOneStep_ = 0;
int SMTCell::metalThreeStep_ = 0;
int SMTCell::realNumTrackV_ = 0;
int SMTCell::realNumPTrackV_ = 0;
int SMTCell::verticalSubGrid_ = 0;
int SMTCell::gcdStep_ = 0;

// Track related info
int SMTCell::numTrack_ = 0;
int SMTCell::numFin_ = 0;
int SMTCell::placementRow_ = 0;
float SMTCell::trackEachRow_ = 0.0;
int SMTCell::trackEachPRow_ = 0;
int SMTCell::numTrackH_ = 0;
int SMTCell::numTrackV_ = 0;
int SMTCell::numMetalLayer_ = 0;
int SMTCell::numPTrackH_ = 0;
int SMTCell::numPTrackV_ = 0;
int SMTCell::lastIdxPMOS_ = -1;
int SMTCell::numInstance_ = 0;
int SMTCell::numNets_org_ = 0;

// Cell related info
int SMTCell::minWidth_ = 0;

// store variable declaration and index
int SMTCell::idx_var_ = 1;
int SMTCell::idx_clause_ = 1;
std::map<std::string, int> SMTCell::h_var = {};
std::map<std::string, int> SMTCell::h_assign = {};
std::map<std::string, int> SMTCell::h_assign_new = {};

// Cell Object related
// ### PIN variables
std::vector<Pin *> SMTCell::pins;
// std::map<unsigned int, int> SMTCell::h_pin_id;
std::map<unsigned int, int> SMTCell::h_InstPin_to_netID = {};
// std::map<unsigned int, int> SMTCell::h_pin_idx;
std::map<unsigned int, int> SMTCell::h_instID_to_pinStart = {};
// std::map<unsigned int, int> SMTCell::h_pinId_idx;
std::map<unsigned int, int> SMTCell::h_pinName_to_idx = {};
std::map<unsigned int, int> SMTCell::h_outpinId_idx = {};
std::map<unsigned int, std::string> SMTCell::h_pin_net = {};

// ### NET variables
std::vector<Net *> SMTCell::nets;
std::map<int, int> SMTCell::h_extnets;
std::map<unsigned int, int> SMTCell::h_netId_to_netIdx;
std::map<unsigned int, int> SMTCell::h_outnets;

// ### INSTANCE variables
std::vector<Instance *> SMTCell::insts;
std::map<unsigned int, int> SMTCell::h_inst_idx;

// ### Partition Info
std::vector<std::tuple<std::string, std::string, int>> SMTCell::inst_partition;
std::map<int, int> SMTCell::h_inst_partition;
std::map<int, std::string> SMTCell::h_sdbInst;
std::vector<std::tuple<int, std::vector<int>, int>> SMTCell::inst_partition_p;
std::vector<std::tuple<int, std::vector<int>, int>> SMTCell::inst_partition_n;

// ### Power Net/Pin Info
std::map<unsigned int, int> SMTCell::h_pin_power;
std::map<unsigned int, int> SMTCell::h_net_power;

// ### Crostalk Mitigation Info
std::map<std::string, int> SMTCell::h_net_track;
// std::map<int, int> SMTCell::h_net_track_t;
std::map<int, std::vector<std::string>> SMTCell::h_track_net;
// std::map<int, int> SMTCell::h_net_track_n; // not used for now
std::map<int, std::string> SMTCell::h_net_opt;

// ### Graph Variable
std::map<Triplet, Vertex *> SMTCell::vertices;
std::vector<UdEdge *> SMTCell::udEdges;
std::vector<Triplet *> SMTCell::boundaryVertices;
std::vector<OuterPin *> SMTCell::outerPins;
std::vector<Triplet *> SMTCell::leftCorners;
std::vector<Triplet *> SMTCell::rightCorners;
std::vector<Triplet *> SMTCell::frontCorners;
std::vector<Triplet *> SMTCell::backCorners;
std::map<std::string, Source *> SMTCell::sources;
std::map<std::string, Sink *> SMTCell::sinks;
// std::vector<Triplet *> SMTCell::subNodes;
std::vector<VirtualEdge *> SMTCell::virtualEdges;
std::map<std::string, std::vector<int>> SMTCell::edge_in;
std::map<std::string, std::vector<int>> SMTCell::edge_out;
std::map<std::string, std::vector<int>> SMTCell::vedge_in;
std::map<std::string, std::vector<int>> SMTCell::vedge_out;

std::string SMTCell::keySON = "pinSON";

// void SMTCell::init() {
//   for (auto const &mt : SMTCell::mapTrack) {
//     SMTCell::h_mapTrack[mt.second] = 1;
//     SMTCell::h_RTrack[mt.first] = mt.second;
//   }

//   for (auto const &nc : SMTCell::numContact) {
//     SMTCell::h_numCon[nc.first] = nc.second - 1;
//   }
// }

void SMTCell::initTrackInfo(const std::string &config_path) {
  std::ifstream config_file(config_path);
  nlohmann::json config = nlohmann::json::parse(config_file);
  config_file.close();

  SMTCell::verticalSubGrid_ = config["MetalOneStep"]["value"];
  SMTCell::metalOneStep_ = config["MetalOneStep"]["value"];
  SMTCell::metalThreeStep_ = config["MetalThreeStep"]["value"];
  SMTCell::numTrack_ = config["NumTrack"]["value"];

  SMTCell::gcdStep_ =
      SMTCell::gcd_helper(SMTCell::metalOneStep_, SMTCell::metalThreeStep_);

  if (SMTCell::numTrack_ == 4) {
    // # Placement vs. Routing Horizontal Track Mapping Array
    SMTCell::mapTrack = {{0, 3}, {1, 2}, {2, 1}, {3, 0}};
    SMTCell::numFin_ = 2;
  } else if (SMTCell::numTrack_ == 5) {
    // # Placement vs. Routing Horizontal Track Mapping Array
    SMTCell::mapTrack = {{0, 4}, {1, 3}, {2, 3}, {3, 1}, {4, 1}, {5, 0}};
    SMTCell::numFin_ = 3;
  } else {
    std::cout << "ERROR: Invalid number of tracks" << std::endl;
    exit(-1);
  }

  for (auto const &mt : SMTCell::mapTrack) {
    SMTCell::h_mapTrack[mt.second] = 1;
    SMTCell::h_RTrack[mt.first] = mt.second;
  }

  for (auto const &nc : SMTCell::numContact) {
    SMTCell::h_numCon[nc.first] = nc.second - 1;
  }
}

int SMTCell::gcd_helper(int a, int b) {
  if (b == 0)
    return a;
  return SMTCell::gcd_helper(b, a % b);
}

void SMTCell::setPlacementRow(int placementRow) {
  SMTCell::placementRow_ = placementRow;
}

void SMTCell::setTrackEachRow(float trackEachRow) {
  SMTCell::trackEachRow_ = trackEachRow;
}

void SMTCell::setTrackEachPRow(int trackEachPRow) {
  SMTCell::trackEachPRow_ = trackEachPRow;
}

void SMTCell::setNumTrackH(int numTrackH) { SMTCell::numTrackH_ = numTrackH; }

void SMTCell::setNumTrackV(int numTrackV) { SMTCell::numTrackV_ = numTrackV; }

void SMTCell::setNumMetalLayer(int numMetalLayer) {
  SMTCell::numMetalLayer_ = numMetalLayer;
}

void SMTCell::setNumPTrackH(int numPTrackH) {
  SMTCell::numPTrackH_ = numPTrackH;
}

void SMTCell::setNumPTrackV(int numPTrackV) {
  SMTCell::numPTrackV_ = numPTrackV;
}

// by default add (4+1)
// replaced by realNumTrackV_
int SMTCell::getBitLengthNumTrackV() {
  if (SMTCell::numTrackV_ > 0) {
    // return bmp::msb(SMTCell::numTrackV_) + 5;
    return bmp::msb(SMTCell::realNumTrackV_) + 5;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before numTrackV is set\n";
    exit(0);
  }
}

// by default add (+1)
int SMTCell::getBitLengthNumTrackH() {
  if (SMTCell::numTrackH_ > 0) {
    return bmp::msb(SMTCell::numTrackH_) + 1;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before numTrackV is set\n";
    exit(0);
  }
}

int SMTCell::getBitLengthNumPTrackH() {
  if (SMTCell::numPTrackH_ > 0) {
    return bmp::msb(SMTCell::numPTrackH_) + 1;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before numPTrackH is set\n";
    exit(0);
  }
}

int SMTCell::getBitLengthTrackEachPRow() {
  if (SMTCell::trackEachPRow_ > 0) {
    return bmp::msb(SMTCell::trackEachPRow_) + 1;
  } else {
    std::cerr << "[ERROR] Calling Bit Length before trackEachPRow is set\n";
    exit(0);
  }
}

void SMTCell::cnt(std::string type, int idx) {
  // $type = @_[0];);
  // $idx = @_[1];
  // Variable
  if (type == "v") {
    switch (idx) {
    case 0:
      SMTCell::c_v_placement_++;
      break;
    case 1:
      SMTCell::c_v_placement_aux_++;
      break;
    case 2:
      SMTCell::c_v_routing_++;
      break;
    case 3:
      SMTCell::c_v_routing_aux_++;
      break;
    case 4:
      SMTCell::c_v_connect_++;
      break;
    case 5:
      SMTCell::c_v_connect_aux_++;
      break;
    case 6:
      SMTCell::c_v_dr_++;
      break;
    default:
      std::cout << "[Warning] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(-1);
    }
  } else if (type == "c") { // Constraints
    switch (idx) {
    case 0:
      SMTCell::c_c_placement_++;
      break;
    case 1:
      SMTCell::c_c_routing_++;
      break;
    case 2:
      SMTCell::c_c_connect_++;
      break;
    case 3:
      SMTCell::c_c_dr_++;
      break;
    case 4:
      std::cout << "[Warning] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(-1);
    }
  } else if (type == "l") { // Literals
    switch (idx) {
    case 0:
      SMTCell::c_l_placement_++;
      break;
    case 1:
      SMTCell::c_l_routing_++;
      break;
    case 2:
      SMTCell::c_l_connect_++;
      break;
    case 3:
      SMTCell::c_l_dr_++;
      break;
    default:
      std::cout << "[Warning] Count Option is Invalid!! [type=" << type
                << ", idx=" << idx << "]\n";
      exit(-1);
    }
  } else {
    std::cout << "[Warning] Count Option is Invalid!! [type=" << type
              << ", idx=" << idx << "]\n";
    exit(-1);
  }
}

std::vector<std::vector<int>> SMTCell::combine(std::vector<int> &l, int n) {
  if (n > l.size()) {
    throw "Insufficient l members";
  }

  if (n <= 1) {
    std::vector<std::vector<int>> result;
    for (int x : l) {
      std::vector<int> temp;
      temp.push_back(x);
      result.push_back(temp);
    }
    return result;
  }

  std::vector<std::vector<int>> comb;
  int val = l[0];
  std::vector<int> rest(l.begin() + 1, l.end());
  auto sub_comb = SMTCell::combine_sub(rest, n - 1);
  for (auto &v : sub_comb) {
    v.insert(v.begin(), val);
    comb.push_back(v);
  }

  return comb;
}

std::vector<std::vector<int>> SMTCell::combine_sub(std::vector<int> &l, int n) {
  if (n > l.size()) {
    throw "Insufficient l members";
  }

  if (n <= 1) {
    std::vector<std::vector<int>> result;
    for (int x : l) {
      std::vector<int> temp;
      temp.push_back(x);
      result.push_back(temp);
    }
    return result;
  }

  std::vector<std::vector<int>> comb;
  for (int i = 0; i + n <= l.size(); ++i) {
    int val = l[i];
    std::vector<int> rest(l.begin() + i + 1, l.end());
    auto sub_comb = SMTCell::combine_sub(rest, n - 1);
    for (auto &v : sub_comb) {
      v.insert(v.begin(), val);
      comb.push_back(v);
    }
  }
  return comb;
}

void SMTCell::reset_cnt() {
  SMTCell::c_v_placement_ = 0;
  SMTCell::c_v_placement_aux_ = 0;
  SMTCell::c_v_routing_ = 0;
  SMTCell::c_v_routing_aux_ = 0;
  SMTCell::c_v_connect_ = 0;
  SMTCell::c_v_connect_aux_ = 0;
  SMTCell::c_v_dr_ = 0;
  SMTCell::c_c_placement_ = 0;
  SMTCell::c_c_routing_ = 0;
  SMTCell::c_c_connect_ = 0;
  SMTCell::c_c_dr_ = 0;
  SMTCell::c_l_placement_ = 0;
  SMTCell::c_l_routing_ = 0;
  SMTCell::c_l_connect_ = 0;
  SMTCell::c_l_dr_ = 0;
}

void SMTCell::reset_var() {
  SMTCell::clear_writeout();
  SMTCell::h_var.clear();
  SMTCell::idx_var_ = 1;
}

void SMTCell::clear_writeout() { SMTCell::writeout = ""; }

void SMTCell::writeConstraint(std::string str) { SMTCell::writeout += str; }

std::string SMTCell::readConstraint() { return SMTCell::writeout; }

bool SMTCell::setVar(std::string varName, int type) {
  // not exist
  if (SMTCell::h_var.find(varName) == SMTCell::h_var.end()) {
    // why this is type not index?
    cnt("v", type);
    SMTCell::h_var[varName] = SMTCell::idx_var_;
    SMTCell::idx_var_++;
    return true;
  }
  return false;
}

bool SMTCell::setVar_wo_cnt(std::string varName, int type) {
  // not exist
  if (SMTCell::h_var.find(varName) == SMTCell::h_var.end()) {
    SMTCell::h_var[varName] = -1;
    return true;
  }
  return false;
}

int SMTCell::getTotalVar() {
  return SMTCell::c_v_placement_ + SMTCell::c_v_placement_aux_ +
         SMTCell::c_v_routing_ + SMTCell::c_v_routing_aux_ +
         SMTCell::c_v_connect_ + SMTCell::c_v_connect_aux_ + SMTCell::c_v_dr_;
}

int SMTCell::getTotalClause() {
  return SMTCell::c_c_placement_ + SMTCell::c_c_routing_ +
         SMTCell::c_c_connect_ + SMTCell::c_c_dr_;
}

int SMTCell::getTotalLiteral() {
  return SMTCell::c_l_placement_ + SMTCell::c_l_routing_ +
         SMTCell::c_l_connect_ + SMTCell::c_l_dr_;
}

void SMTCell::dump_summary() {
  std::cout << "a     ########## Summary ##########\n";
  std::cout << "a     # var for placement       = " << SMTCell::c_v_placement_
            << "\n";
  std::cout << "a     # var for placement(aux)  = "
            << SMTCell::c_v_placement_aux_ << "\n";
  std::cout << "a     # var for routing         = " << SMTCell::c_v_routing_
            << "\n";
  std::cout << "a     # var for routing(aux)    = " << SMTCell::c_v_routing_aux_
            << "\n";
  std::cout << "a     # var for design rule     = " << SMTCell::c_v_dr_ << "\n";
  std::cout << "a     # literals for placement   = " << SMTCell::c_l_placement_
            << "\n";
  std::cout << "a     # literals for routing     = " << SMTCell::c_l_routing_
            << "\n";
  std::cout << "a     # literals for design rule = " << SMTCell::c_l_dr_
            << "\n";
  std::cout << "a     # clauses for placement   = " << SMTCell::c_c_placement_
            << "\n";
  std::cout << "a     # clauses for routing     = " << SMTCell::c_c_routing_
            << "\n";
  std::cout << "a     # clauses for design rule = " << SMTCell::c_c_dr_ << "\n";
}

std::vector<int> SMTCell::getAvailableNumFinger(int w,
                                                int track_each_placement_row) {
  std::vector<int> numFinger;
  for (int i = 0; i < track_each_placement_row; i++) {
    if (w % (track_each_placement_row - i) == 0) {
      numFinger.push_back(w / (track_each_placement_row - i));
      break;
    }
  }
  return numFinger;
}