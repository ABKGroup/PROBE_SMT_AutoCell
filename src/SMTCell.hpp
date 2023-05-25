#define FMT_HEADER_ONLY
#pragma once
#define FMT_HEADER_ONLY
#include <boost/multiprecision/integer.hpp> // for returning bit length
#include <fmt/core.h>
#include <fmt/format.h>
#include <fstream>
#include <iostream>
#include <map>
#include <nlohmann/json.hpp>
#include <string>
#include <vector>

#include "graph.hpp"
#include "obj.hpp"

namespace bmp = boost::multiprecision;

class SMTCell {
  /*
    Wrapper Class for utility functions
  */
public:
  SMTCell();

  static bool DEBUG;

  // static void init();

  // will read track height + set Gear Ratio info
  static void initTrackInfo(const std::string &config_path);

  static int getNumTrack() { return numTrack_; }

  static int getNumFin() { return numFin_; }

  // Gear Ratio specific config
  static void setRealNumTrackV(int realNumTrackV) {
    realNumTrackV_ = realNumTrackV;
  }

  // an helper function for finding GCD between M1 and M3
  static int gcd_helper(int a, int b);

  static int getGCDStep() { return gcdStep_; }

  static int getRealNumTrackV() { return realNumTrackV_; }

  static void setRealNumPTrackV(int realNumPTrackV) {
    realNumPTrackV_ = realNumPTrackV;
  }

  // for retrieving the real track height (w/o power rails)
  static int getRealTrackHeight() {
    if (numTrack_ == 4) {
      return 3;
    } else if (numTrack_ == 5) {
      return 4;
    } else {
      fmt::print("[ERROR] numTrack_ is not 4 or 5");
      exit(-1);
    }
  }

  static int getRealNumPTrackV() { return realNumPTrackV_; }

  static int getVerticalSubGrid() { return verticalSubGrid_; }

  static void setMetalOneStep(int metalOneStep) {
    metalOneStep_ = metalOneStep;
  }

  static int getMetalOneStep() { return metalOneStep_; }

  static void setMetalThreeStep(int metalThreeStep) {
    metalThreeStep_ = metalThreeStep;
  }

  static int getMetalThreeStep() { return metalThreeStep_; }

  // num of track related
  static int getPlacementRow() { return placementRow_; };

  static int getTrackEachPRow() { return trackEachPRow_; };

  static float getTrackEachRow() { return trackEachRow_; };

  static int getNumTrackH() { return numTrackH_; };

  static int getNumTrackV() { return numTrackV_; };

  static int getNumMetalLayer() { return numMetalLayer_; };

  static int getNumPTrackH() { return numPTrackH_; };

  static int getNumPTrackV() { return numPTrackV_; };

  static void setPlacementRow(int placementRow);

  static void setTrackEachPRow(int trackEachPRow);

  static void setTrackEachRow(float trackEachRow);

  static void setNumTrackH(int numTrackH);

  static void setNumTrackV(int numTrackV);

  static void setNumMetalLayer(int numMetalLayer);

  static void setNumPTrackH(int numPTrackH);

  static void setNumPTrackV(int numPTrackV);

  static int getBitLengthNumTrackV();

  static int getBitLengthNumTrackH();

  static int getBitLengthNumPTrackH();

  static int getBitLengthTrackEachPRow();

  static void setLastIdxPMOS(int lastIdxPMOS) { lastIdxPMOS_ = lastIdxPMOS; }

  static int getLastIdxPMOS() { return lastIdxPMOS_; }

  static int getLastRowIdx() { return numTrackH_ - 3; }

  static int getLastColIdx() { return numTrackV_ - 1; }

  static void incrementNumNetsOrg() { numNets_org_++; }

  static int getNumNetsOrg() { return numNets_org_; }

  // PMOS/NMOS/Instance count
  static int getNumPMOS() { return lastIdxPMOS_ + 1; }

  static int getNumNMOS() { return numInstance_ - lastIdxPMOS_ - 1; }

  static void incrementNumInstance() { numInstance_++; }

  static int getNumInstance() { return numInstance_; }

  // Gate/Source/Drain Column
  static bool ifGCol(int col) {
    return col % (2 * SMTCell::getMetalOneStep()) == 0;
  }

  static bool ifSDCol(int col) {
    return col % (2 * SMTCell::getMetalOneStep()) == SMTCell::getMetalOneStep();
  }

  // return if PMOS or NMOS based on inst Idx (could be simplified further)
  static bool ifInstPMOS(int instIdx) { return instIdx <= lastIdxPMOS_; }

  static bool ifInstNMOS(int instIdx) { return !(instIdx <= lastIdxPMOS_); }

  static bool ifPinInstPMOS(int pinIdx) {
    return getPinInstIdx(pinIdx) <= lastIdxPMOS_;
  }

  static bool ifPinInstPMOS(std::string pinName) {
    return getPinInstIdx(pinName) <= lastIdxPMOS_;
  }

  static bool ifPinInstPMOS(Pin *p) { return getPinInstIdx(p) <= lastIdxPMOS_; }

  static bool ifPinInstNMOS(int pinIdx) {
    return !(getPinInstIdx(pinIdx) <= lastIdxPMOS_);
  }

  static bool ifPinInstNMOS(std::string pinName) {
    return !(getPinInstIdx(pinName) <= lastIdxPMOS_);
  }

  static bool ifPinInstNMOS(Pin *p) {
    return !(getPinInstIdx(p) <= lastIdxPMOS_);
  }

  // Cell Object related
  // ######################### Pin related
  static void addPin(Pin *pin_obj) { pins.push_back(pin_obj); }

  // overload to directly add pin
  static void addPin(std::string pinName, std::string netID, std::string pinIO,
                     int pinLength, int pinXpos, std::vector<int> pinYpos,
                     std::string instID, std::string pinType) {
    pins.push_back(new Pin(pinName, netID, pinIO, pinLength, pinXpos, pinYpos,
                           instID, pinType));
  }

  // retrieve pin obj by pin idx
  static Pin *getPin(int pinIdx) { return pins[pinIdx]; }

  // retrieve pin obj by pinName
  static Pin *getPin(std::string pinName) {
    return pins[h_pinName_to_idx[Pin::hash(pinName.data())]];
  }

  static Pin *popLastPin() {
    Pin *tmp_pin = pins.back();
    pins.pop_back();

    return tmp_pin;
  }

  static int getPinCnt() { return pins.size(); }

  // set pin NetID
  static void setPinNetID(int pinIdx, std::string pin_netID) {
    pins[pinIdx]->setNetID(pin_netID);
  }

  // set pin type
  static void setPinType(int pinIdx, std::string pin_type) {
    pins[pinIdx]->setPinType(pin_type);
  }

  // set pin type
  static void setPinIO(int pinIdx, std::string pinIO) {
    pins[pinIdx]->setPinIO(pinIO);
  }

  static void addOutPinIdx(std::string pinName, int pinIdx) {
    h_outpinId_idx[Pin::hash(pinName.data())] = pinIdx;
  }

  static int getOutPinIdx(std::string pinName) {
    return h_outpinId_idx[Pin::hash(pinName.data())];
  }

  static bool ifOuterPin(std::string pinName) {
    return h_outpinId_idx.find(Pin::hash(pinName.data())) !=
           h_outpinId_idx.end();
  }

  // if powerpin, assign to 1, no need to retrieve
  static void addPowerPin(std::string pinName) {
    h_pin_power[Pin::hash(pinName.data())] = 1;
  }

  static bool ifPowerPin(std::string pinName) {
    return h_pin_power.find(Pin::hash(pinName.data())) != h_pin_power.end();
  }

  // pinName to pin index in pins
  static int getPinIdx(std::string pinName) {
    return h_pinName_to_idx.at(Pin::hash(pinName.data()));
  }

  static void setPinIdx(std::string pinName, int pinIdx) {
    h_pinName_to_idx[Pin::hash(pinName.data())] = pinIdx;
  }
  //   h_pinName_to_idx[Pin::hash(pinName.data())] = pinIdx;
  // }

  static void removePowerPin() {
    std::vector<Pin *> tmp_pins;
    std::vector<Net *> nets_sorted;

    int pinIDX = 0;

    for (Pin *p : pins) {
      if (!ifPowerPin(p->getPinName())) {
        tmp_pins.push_back(p);
        setPinIdx(p->getPinName(), pinIDX);

        if (p->getPinType() != "S" && p->getPinType() != "D" &&
            p->getPinType() != "G") {
          addOutPinIdx(p->getPinName(), pinIDX);
        }
        pinIDX++;
      }
    }
    pins.clear();
    pins = tmp_pins;
  }

  static void removePowerNet() {
    std::vector<Net *> tmp_nets;

    int tmp_net_idx = 0;
    for (Net *n : nets) {
      if (!ifPwrNet(n->getNetName())) {
        tmp_nets.push_back(n);
        setNetIdx(n->getNetID(), tmp_net_idx);
        tmp_net_idx++;
      }
    }
    nets.clear();
    nets = tmp_nets;
  }
  static void dumpPins() {
    fmt::print("[DEBUG] pins...\n");
    for (Pin *p : pins) {
      p->dump();
    }

    fmt::print("[DEBUG] h_InstPin_to_netID...\n");
    for (auto const &v : h_InstPin_to_netID) {
      fmt::print("  {} => {}\n", v.first, v.second);
    }

    fmt::print("[DEBUG] h_instID_to_pinStart...\n");
    for (auto const &v : h_instID_to_pinStart) {
      fmt::print("  {} => {}\n", v.first, v.second);
    }

    fmt::print("[DEBUG] h_pinName_to_idx...\n");
    for (auto const &v : h_pinName_to_idx) {
      fmt::print("  {} => {}\n", v.first, v.second);
    }
  }

  // ######################### Instance related
  static void addInst(Instance *inst_obj) { insts.push_back(inst_obj); }

  static void addInst(std::string instName, std::string instType, int instWidth,
                      int instY) {
    insts.push_back(new Instance(instName, instType, instWidth, instY));
  }

  static Instance *getInst(int instIdx) { return insts[instIdx]; }

  static Instance *getInst(std::string instName) {
    return insts[h_inst_idx.at(Instance::hash(instName.data()))];
  }

  // retrieve instance obj directly from pinName
  static Instance *getPinInst(std::string pinName) {
    return insts[h_inst_idx.at(
        Instance::hash(getPin(pinName)->getInstID().data()))];
  }

  static Instance *getPinInst(int pinIdx) {
    return insts[h_inst_idx.at(
        Instance::hash(getPin(pinIdx)->getInstID().data()))];
  }

  static int getPinInstIdx(std::string pinName) {
    return h_inst_idx.at(Instance::hash(getPin(pinName)->getInstID().data()));
  }

  static int getPinInstIdx(int pinIdx) {
    return h_inst_idx.at(Instance::hash(getPin(pinIdx)->getInstID().data()));
  }

  static int getPinInstIdx(Pin *p) {
    return h_inst_idx.at(Instance::hash(p->getInstID().data()));
  }

  // if instance exists
  static bool ifInst(std::string instName) {
    return h_inst_idx.find(Instance::hash(instName.data())) != h_inst_idx.end();
  }

  static bool ifPinInst(int pinIdx) {
    return h_inst_idx.find(Instance::hash(
               getPin(pinIdx)->getInstID().data())) != h_inst_idx.end();
  }

  // Retrieve instance name to first pin of this inst index inside pins
  // From this start index and #finger, iterate all possible pins
  static int getStartPinIndex(std::string instID) {
    return h_instID_to_pinStart.at(Instance::hash(instID.data()));
  }

  static void setStartPinIndex(std::string instName, int pinIdx) {
    h_instID_to_pinStart[Instance::hash(instName.data())] = pinIdx;
  }

  static void setInstIdx(std::string instName, int instIdx) {
    h_inst_idx[Instance::hash(instName.data())] = instIdx;
  }

  static int getInstIdx(std::string instName) {
    return h_inst_idx[Instance::hash(instName.data())];
  }

  static int getInstCnt() { return insts.size(); }

  // ######################### Net related
  static void addNet(Net *net_obj) { nets.push_back(net_obj); }

  static void addNet(std::string netName, std::string netID, int N_pinNets,
                     std::string source_ofNet, int numSinks,
                     std::vector<std::string> sinks_inNet,
                     std::vector<std::string> pins_inNet) {
    nets.push_back(new Net(netName, netID, N_pinNets, source_ofNet, numSinks,
                           sinks_inNet, pins_inNet));
  }

  static Net *getNet(int netIdx) { return nets[netIdx]; }

  static int getNetCnt() { return nets.size(); }

  // this is not the index in nets, but the "net#" in pinlayout
  static void addExtNet(int net_Idx) { h_extnets[net_Idx] = 1; }

  static int getNetIdx(std::string netId) {
    return h_netId_to_netIdx.at(Net::hash(netId.data()));
  }

  static void setNetIdx(std::string netId, int netIdx) {
    h_netId_to_netIdx[Net::hash(netId.data())] = netIdx;
  }

  // from pin

  // temp solution for flow writer
  static std::map<int, int> getExtNet() { return h_extnets; }

  // static void addPwrNet(int net_Idx) { h_net_power[net_Idx] = 1; }

  static void addPwrNet(std::string netID) {
    h_net_power[Net::hash(netID.data())] = 1;
  }

  static bool ifPwrNet(std::string netName) {
    return h_net_power.find(Net::hash(netName.data())) != h_net_power.end();
  }

  static int getExtNetCnt() { return h_extnets.size(); }

  // h_outnets is the net that is connected to output pin
  static void addOutNet(int netIdx) { h_outnets[netIdx] = 1; }

  static int getOutNetCnt() { return h_outnets.size(); }

  static int getOutNet(int netIdx) { return h_outnets[netIdx]; }

  static int ifOutNet(std::string netID) {
    return h_outnets.find(Net::hash(netID.data())) != h_outnets.end();
  }

  // pin related instance name (or ext net) + (_S/G/D/A/B/Y) to net id
  static int getInstWPinNetID(std::string instWPin) {
    return h_InstPin_to_netID.at(Instance::hash(instWPin.data()));
  }

  static void setInstWPinNetIdx(std::string instWPin, int netIdx) {
    h_InstPin_to_netID[Instance::hash(instWPin.data())] = netIdx;
  }

  // count variable
  static void cnt(std::string type, int idx);

  // reset var count
  static void reset_var();

  static void reset_cnt();

  static void clear_writeout();

  // hold constraint (does not directly write to .smt2)
  static void writeConstraint(std::string str);

  // read constraint
  static std::string readConstraint();

  // set all track related info
  static void set_numTracks(int placementRow, int trackEachRow,
                            int trackEachPRow, int numTrackH, int numTrackV,
                            int numMetalLayer, int numPTrackH, int numPTrackV);

  // Declare a variable
  static bool setVar(std::string varName, int type);

  // Declare a variable without counting
  static bool setVar_wo_cnt(std::string varName, int type);

  static int assignVar(std::string varName) {
    if (!SMTCell::ifAssigned(varName)) {
      // if(!exists($h_assign{$tmp_str}))
      setVar(varName, 2);
      return 1;
    } else if (SMTCell::ifAssignedTrue(varName)) {
      // if(exists($h_assign{$tmp_str}) && $h_assign{$tmp_str} eq 1)
      setVar_wo_cnt(varName, 0);
      return 0;
    }
    return -1;
  }

  // if var in h_assign
  static bool ifAssigned(std::string varName) {
    return SMTCell::h_assign.find(varName) != SMTCell::h_assign.end();
  }

  static int getAssignedCnt() { return h_assign.size(); }

  static int getNewAssignedCnt() { return h_assign_new.size(); }

  // if var in h_assign and = 1, then assert True
  static bool ifAssignedTrue(std::string varName) {
    return (SMTCell::h_assign.find(varName) != SMTCell::h_assign.end() &&
            h_assign.at(varName) == 1);
  }

  // if var in h_assign and = 0, then assert False
  static bool ifAssignedFalse(std::string varName) {
    return (SMTCell::h_assign.find(varName) != SMTCell::h_assign.end() &&
            h_assign.at(varName) == 0);
  }

  // get the assigned value
  static int getAssigned(std::string varName) {
    if (ifAssigned(varName)) {
      return SMTCell::h_assign.at(varName);
    }
    return -1;
  }

  static void assignFalseVar(std::string varName) {
    SMTCell::h_assign[varName] = 0;
  }

  // check h_assign, then assign either to h_assign_new or h_assign
  static void assignTrueVar(std::string varName, int val, bool toNew) {
    // if not exist
    if (SMTCell::h_assign.find(varName) == SMTCell::h_assign.end()) {
      if (toNew) {
        SMTCell::h_assign_new[varName] = val;
      } else {
        SMTCell::h_assign[varName] = val;
      }
    }
  }
  // check h_assign with "$vName\_$udEdges[$edge_out{$vName}[$i]][2]" and assign
  // "N$nets[$netIndex][1]\_C$commodityIndex\_E_$vName\_$udEdges[$edge_out{$vName}[$i]][2]"
  static void assignTrueVar(std::string netID, int commodityIndex,
                            std::string vName1, std::string vName2, int val,
                            bool toNew) {
    // if not exist
    std::string varName = fmt::format("{}_{}", vName1, vName2);

    if (SMTCell::h_assign.find(varName) == SMTCell::h_assign.end()) {
      std::string variable_name =
          fmt::format("N{}_C{}_E_{}_{}", netID, commodityIndex, vName1, vName2);
      if (toNew) {
        SMTCell::h_assign_new[variable_name] = val;
      } else {
        SMTCell::h_assign[variable_name] = val;
      }
    }
  }

  // Merge assignment information
  static void mergeAssignment() {
    if (h_assign_new.size() > 0) {
      for (const auto &assign_pair : h_assign_new) {
        h_assign[assign_pair.first] = h_assign_new.at(assign_pair.first);
      }
      h_assign_new.clear();
    }
  }

  // If variable declared
  static bool ifVar(std::string varName) {
    return SMTCell::h_var.find(varName) != SMTCell::h_var.end();
  }

  static void flushConstraint(FILE *fp) { fmt::print(fp, readConstraint()); }

  static void flushVarAndConstraint(FILE *fp, int BCP_Parameter) {
    // define boolean
    for (auto const &e : h_var) {
      fmt::print(fp, "(declare-const {} Bool)\n", e.first);
    }

    // write constraints
    flushConstraint(fp);

    // assign T/F
    for (auto const &e : h_assign) {
      if (e.second == 1) {
        fmt::print(fp, "(assert (= {} true))\n", e.first);
      }
    }

    // BCP
    if (BCP_Parameter == 0) {
      fmt::print(fp, ";WO BCP\n");
      for (auto const &e : h_assign_new) {
        if (e.second == 1) {
          fmt::print(fp, "(assert (= {} true))\n", e.first);
        } else {
          fmt::print(fp, "(assert (= {} false))\n", e.first);
        }
      }
    }
  }

  static int getVarCnt() { return h_var.size(); }
  static int getAssignCnt() { return h_assign.size(); }
  static int getCandidateAssignCnt() { return h_assign_new.size(); }

  // Retrieve var, clause, literal
  static int getTotalVar();

  static int getTotalClause();

  static int getTotalLiteral();

  // Dump
  static void dump_summary();

  static void dump_h_assign() {
    for (auto const &assign : SMTCell::h_assign) {
      fmt::print("  {} => {}\n", assign.first, assign.second);
    }
  }

  static void dump_h_netId_to_netIdx() {
    for (auto const &assign : SMTCell::h_netId_to_netIdx) {
      fmt::print("  {} => {}\n", assign.first, assign.second);
    }
  }

  // Retrieve finger count based on transistor width
  static std::vector<int> getAvailableNumFinger(int w,
                                                int track_each_placement_row);

  static std::vector<std::vector<int>> combine(std::vector<int> &l, int n);
  static std::vector<std::vector<int>> combine_sub(std::vector<int> &l, int n);

  // Track information
  static bool findTrack(int k) {
    return h_mapTrack.find(k) != h_mapTrack.end();
  }

  static int getRoutingTrack(int k) { return h_RTrack.at(k); }

  static int getConnection(int k) { return h_numCon.at(k); }

  // retrieve min(PMOS_width, NMOS_width)
  static void setMOSMinWidth() {
    int tmp_minWidth = 0;

    for (int i = 0; i <= getLastIdxPMOS(); i++) {
      std::vector<int> tmp_finger =
          getAvailableNumFinger(getInst(i)->getInstWidth(), getTrackEachPRow());
      tmp_minWidth += 2 * tmp_finger[0];
    }

    minWidth_ = tmp_minWidth;
    tmp_minWidth = 0;

    for (int i = getNumPMOS(); i < getNumInstance(); i++) {
      std::vector<int> tmp_finger =
          getAvailableNumFinger(getInst(i)->getInstWidth(), getTrackEachPRow());
      tmp_minWidth += 2 * tmp_finger[0];
    }

    if (tmp_minWidth > minWidth_) {
      minWidth_ = tmp_minWidth;
    }
  }

  static int getMOSMinWidth() { return minWidth_; }
  // ### Graph Variable
  // Vertex
  static void addVertex(Triplet key, Vertex *val) { vertices[key] = val; }

  static Vertex *getVertex(Triplet key) { return vertices[key]; }

  static int getVertexCnt() { return vertices.size(); }

  static bool ifVertex(Triplet key) {
    return vertices.find(key) != vertices.end();
  }

  static void dump_vertices() {
    for (auto v : vertices) {
      fmt::print("{}\n", v.first.getVname());
      v.second->dump();
    }
  }

  // UdEdge
  static void addUdEdge(UdEdge *udedge) { udEdges.push_back(udedge); }

  static UdEdge *getUdEdge(int udEdgeIdx) { return udEdges[udEdgeIdx]; }

  static int getUdEdgeCnt() { return udEdges.size(); }

  static void dump_udEdges() {
    for (auto udEdge : udEdges) {
      udEdge->dump();
    }
  }

  // boundaryVertices
  static void addBoundaryVertex(Triplet *boundaryVertex) {
    boundaryVertices.push_back(boundaryVertex);
  }

  static Triplet *getBoundaryVertex(int idx) { return boundaryVertices[idx]; }

  static int getBoundaryVertexCnt() { return boundaryVertices.size(); }

  static std::vector<Triplet *> copyBoundaryVertex() {
    std::vector<Triplet *> tmp_subNodes;
    tmp_subNodes.assign(boundaryVertices.begin(), boundaryVertices.end());
    return tmp_subNodes;
  }

  static void dump_boundaryVertices() {
    for (auto bv : boundaryVertices) {
      fmt::print("  {}\n", bv->getVname());
    }
  }

  // outerPins
  static void addOuterPin(OuterPin *outerPin) { outerPins.push_back(outerPin); }

  static OuterPin *getOuterPin(int idx) { return outerPins[idx]; }

  static int getOuterPinCnt() { return outerPins.size(); }

  static std::string dump_SON() {
    std::string tmp_str = "";
    for (auto op : outerPins) {
      // 0 : Pin number , 1 : net number
      tmp_str += fmt::format("{} ", op->getPinName());
    }
    return tmp_str;
  }

  static std::string dump_SON_detail() {
    std::string tmp_str = "";
    for (auto op : outerPins) {
      // 0 : Net number , 1 : Commodity number
      tmp_str += fmt::format(" {}={} ", op->getNetID(), op->getCommodityInfo());
    }
    return tmp_str;
  }

  // leftCorners
  static void addLeftCorner(Triplet *leftCorner) {
    leftCorners.push_back(leftCorner);
  }

  static Triplet *getLeftCorner(int idx) { return leftCorners[idx]; }

  static int getLeftCornerCnt() { return leftCorners.size(); }

  // rightCorners
  static void addRightCorner(Triplet *rightCorner) {
    rightCorners.push_back(rightCorner);
  }

  static Triplet *getRightCorner(int idx) { return rightCorners[idx]; }

  static int getRightCornerCnt() { return rightCorners.size(); }

  // frontCorners
  static void addFrontCorner(Triplet *frontCorner) {
    frontCorners.push_back(frontCorner);
  }

  static Triplet *getFrontCorner(int idx) { return frontCorners[idx]; }

  static int getFrontCornerCnt() { return frontCorners.size(); }

  // backCorners
  static void addBackCorner(Triplet *backCorner) {
    backCorners.push_back(backCorner);
  }

  static Triplet *getBackCorner(int idx) { return backCorners[idx]; }

  static int getBackCornerCnt() { return backCorners.size(); }

  // source
  static void addSource(std::string key, Source *source) {
    sources[key] = source;
  }

  static Source *getSource(std::string key) { return sources[key]; }

  static int getSourceCnt() { return sources.size(); }

  static bool ifSource(std::string key) {
    return sources.find(key) != sources.end();
  }

  static std::string dump_sources() {
    std::string tmp_str = "";
    for (auto s : sources) {
      tmp_str += fmt::format("{} ", s.first);
    }
    return tmp_str;
  }

  // sink
  static void addSink(std::string key, Sink *sink) { sinks[key] = sink; }

  static Sink *getSink(std::string key) { return sinks[key]; }

  static int getSinkCnt() { return sinks.size(); }

  static bool ifSink(std::string key) { return sinks.find(key) != sinks.end(); }

  static std::string dump_sinks() {
    std::string tmp_str = "";
    for (auto s : sinks) {
      tmp_str += fmt::format("{} ", s.first);
    }
    return tmp_str;
  }

  // virtualEdge
  static void addVirtualEdge(VirtualEdge *virtualEdge) {
    virtualEdges.push_back(virtualEdge);
  }

  static VirtualEdge *getVirtualEdge(int idx) { return virtualEdges[idx]; }

  static int getVirtualEdgeCnt() { return virtualEdges.size(); }

  static void dump_virtualEdges() {
    for (auto ve : virtualEdges) {
      ve->dump();
    }
  }

  // edge_in
  static void addEdgeIn(std::string key, int val) {
    edge_in[key].push_back(val);
  }

  static std::vector<int> getEdgeIn(std::string key) { return edge_in[key]; }

  static int getEdgeInCnt() { return edge_in.size(); }

  static bool ifEdgeIn(std::string pName) {
    return edge_in.find(pName) != edge_in.end();
  }

  static void dump_edge_in() {
    for (auto ei : edge_in) {
      fmt::print("  {} : ", ei.first);
      for (auto e : ei.second) {
        fmt::print("{} ", e);
      }
      fmt::print("\n");
    }
  }

  // edge_out
  static void addEdgeOut(std::string key, int val) {
    edge_out[key].push_back(val);
  }

  static std::vector<int> getEdgeOut(std::string key) { return edge_out[key]; }

  static int getEdgeOutCnt() { return edge_out.size(); }

  static std::string getKeySON() { return keySON; }

  static bool ifEdgeOut(std::string pName) {
    return edge_out.find(pName) != edge_out.end();
  }

  static void dump_edge_out() {
    for (auto eo : edge_out) {
      fmt::print("  {} : ", eo.first);
      for (auto e : eo.second) {
        fmt::print("{} ", e);
      }
      fmt::print("\n");
    }
  }

  // vedge_in
  static void addVEdgeIn(std::string key, int val) {
    vedge_in[key].push_back(val);
  }

  static std::vector<int> getVEdgeIn(std::string key) { return vedge_in[key]; }

  static int getVEdgeInCnt() { return vedge_in.size(); }

  static bool ifVEdgeIn(std::string pName) {
    return vedge_in.find(pName) != vedge_in.end();
  }

  // vedge_out
  static void addVEdgeOut(std::string key, int val) {
    vedge_out[key].push_back(val);
  }

  static std::vector<int> getVEdgeOut(std::string key) {
    return vedge_out[key];
  }

  static int getVEdgeOutCnt() { return vedge_out.size(); }

  static bool ifVEdgeOut(std::string pName) {
    return vedge_out.find(pName) != vedge_out.end();
  }

  static void addInstPartition(int idx, std::string instName,
                               std::string instType, int instGroup) {
    inst_partition.push_back(std::make_tuple(instName, instType, instGroup));
    h_inst_partition[idx] = instGroup;
  }

  static int getInstPartitionGroupIdx(int idx) { return h_inst_partition[idx]; }

  static bool ifInstPartition(int idx) {
    return h_inst_partition.find(idx) != h_inst_partition.end();
  }

  static void sortInstPartition() {
    std::sort(inst_partition.begin(), inst_partition.end(),
              [](const std::tuple<std::string, std::string, int> &a,
                 const std::tuple<std::string, std::string, int> &b) {
                return std::get<2>(a) < std::get<2>(b);
              });
  }

  static int getInstPartitionCnt() { return inst_partition.size(); }

  static std::string getInstPartitionName(int idx) {
    return std::get<0>(inst_partition[idx]);
  }

  static std::string getInstPartitionType(int idx) {
    return std::get<1>(inst_partition[idx]);
  }

  static int getInstPartitionGroup(int idx) {
    return std::get<2>(inst_partition[idx]);
  }

  static void dump_InstPartition() {
    for (auto i : inst_partition) {
      std::cout << std::get<0>(i) << " " << std::get<1>(i) << " "
                << std::get<2>(i) << std::endl;
    }
  }

  static void dump_InstPartitionPMOS() {
    for (auto i : inst_partition_p) {
      std::cout << "[" << std::endl;
      std::cout << "  " << std::get<0>(i) << std::endl;
      std::cout << "  [" << std::endl;
      // print the inst indices
      for (auto j : std::get<1>(i)) {
        std::cout << "  " << j << std::endl;
      }
      std::cout << "  ]" << std::endl;
      // print the minWidth
      std::cout << "  " << std::get<2>(i) << std::endl;
      std::cout << "]" << std::endl;
    }
  }

  static void dump_InstPartitionNMOS() {
    for (auto i : inst_partition_n) {
      std::cout << "[" << std::endl;
      std::cout << "  " << std::get<0>(i) << std::endl;
      std::cout << "  [" << std::endl;
      // print the inst indices
      for (auto j : std::get<1>(i)) {
        std::cout << "  " << j << std::endl;
      }
      std::cout << "  ]" << std::endl;
      // print the minWidth
      std::cout << "  " << std::get<2>(i) << std::endl;
      std::cout << "]" << std::endl;
    }
  }

  // PMOS partition
  static void addInstPartitionPMOS(int groupIdx, std::vector<int> instIdices,
                                   int minWidth) {
    inst_partition_p.push_back(std::make_tuple(groupIdx, instIdices, minWidth));
  }

  static int getPInstPartitionGroupIdx(int idx) {
    return std::get<0>(inst_partition_p[idx]);
  }

  static int getPInstPartitionMinWidth(int idx) {
    return std::get<2>(inst_partition_p[idx]);
  }

  static int getPInstPartitionCnt() { return inst_partition_p.size(); }

  static int getPInstPartitionInstIndicesCnt(int idx) {
    return std::get<1>(inst_partition_p[idx]).size();
  }

  static std::vector<int> getPInstPartitionInstIndices(int idx) {
    return std::get<1>(inst_partition_p[idx]);
  }

  static int getPInstPartitionInstIdx(int idx, int idx2) {
    return std::get<1>(inst_partition_p[idx])[idx2];
  }

  // NMOS partition
  static void addInstPartitionNMOS(int groupIdx, std::vector<int> instIdices,
                                   int minWidth) {
    inst_partition_n.push_back(std::make_tuple(groupIdx, instIdices, minWidth));
  }

  static int getNInstPartitionGroupIdx(int idx) {
    return std::get<0>(inst_partition_n[idx]);
  }

  static int getNInstPartitionMinWidth(int idx) {
    return std::get<2>(inst_partition_n[idx]);
  }

  static int getNInstPartitionCnt() { return inst_partition_n.size(); }

  static std::vector<int> getNInstPartitionInstIndices(int idx) {
    return std::get<1>(inst_partition_n[idx]);
  }

  static int getNInstPartitionInstIdx(int idx, int idx2) {
    return std::get<1>(inst_partition_n[idx])[idx2];
  }

  static int getNInstPartitionInstIndicesCnt(int idx) {
    return std::get<1>(inst_partition_n[idx]).size();
  }

  // for Crosstalk mitigation Net assign
  // netTrack is just row number
  static void addSpNet(std::string netIdx) { h_net_track[netIdx] = 1; }

  static int getSpNetCnt() { return h_net_track.size(); }

  static std::map<std::string, int> getSPNet() { return h_net_track; }

  static bool ifSpNet(int netIdx) {
    return h_net_track.find(getNet(netIdx)->getNetID()) != h_net_track.end();
  }

  static void dump_SPNet() {
    for (auto i : h_net_track) {
      std::cout << i.first << " " << i.second << std::endl;
    }
  }

  // for Crosstalk mitigation Track assign
  // netTrack is just row number
  static void addSpTrack(int netTrack, std::string netIdx) {
    if (h_track_net.find(netTrack) == h_track_net.end()) {
      h_track_net[netTrack] = std::vector<std::string>();
    }
    h_track_net[netTrack].push_back(netIdx);
  }

  static int getSpTrackCnt() { return h_track_net.size(); }

  static std::map<int, std::vector<std::string>> getSPTrack() {
    return h_track_net;
  }

  // if this row is used for special net
  static bool ifSpTrack(int netTrack) {
    return h_track_net.find(netTrack) != h_track_net.end();
  }

  static std::vector<std::string> getSpTrackNet(int netTrack) {
    return h_track_net.at(netTrack);
  }

  // if this net and this row is used for special net
  static bool ifSpTrackNet(int netTrack, int netIdx) {
    if (SMTCell::ifSpTrack(netTrack) == false)
      return false;
    // fmt::print ("searching row: {}\n", netTrack);
    for (std::string netID : h_track_net.at(netTrack)) {
      // matching netID which is a std::string
      if (netID == SMTCell::getNet(netIdx)->getNetID()) {
        // fmt::print ("found netID: {}\n", netID);
        return true;
      }
    }
    return false;
  }

  static void dump_SpTrack() {
    for (auto i : h_track_net) {
      std::cout << "[" << std::endl;
      std::cout << "  " << i.first << std::endl;
      std::cout << "  [" << std::endl;
      for (auto j : i.second) {
        std::cout << "  " << j << std::endl;
      }
      std::cout << "  ]" << std::endl;
      std::cout << "]" << std::endl;
    }
  }

  // SDB Possible Cell Info
  static void addSDBInst(int idx, std::string instName) {
    h_sdbInst[idx] = instName;
  }

  static bool ifSDBInst(int idx) {
    return h_sdbInst.find(idx) != h_sdbInst.end();
  }

  static void addNetOpt(int netIdx, std::string opt) {
    h_net_opt[netIdx] = opt;
  }

  static std::string getNetOpt(int netIdx) { return h_net_opt.at(netIdx); }

  static int getNetOptCnt() { return h_net_opt.size(); }

private:
  // hold all constraints to write out to smt2
  static std::string writeout;

  // Placement vs. Routing Horizontal Track Mapping Array [Placement, Routing]
  static std::map<int, int> mapTrack;

  // Number of Routing Contact for Each Width of FET
  static std::map<int, int> numContact;
  static std::map<int, int> h_mapTrack;
  static std::map<int, int> h_RTrack;
  static std::map<int, int> h_numCon;

  // cnt function specific variables
  static int c_v_placement_;
  static int c_v_placement_aux_;
  static int c_v_routing_;
  static int c_v_routing_aux_;
  static int c_v_connect_;
  static int c_v_connect_aux_;
  static int c_v_dr_;
  static int c_c_placement_;
  static int c_c_routing_;
  static int c_c_connect_;
  static int c_c_dr_;
  static int c_l_placement_;
  static int c_l_routing_;
  static int c_l_connect_;
  static int c_l_dr_;

  // store variable declaration and index
  static int idx_var_;
  static int idx_clause_;
  static std::map<std::string, int> h_var;
  static std::map<std::string, int> h_assign;     // pre writeout
  static std::map<std::string, int> h_assign_new; // post writeout

  // Gear Ratio related info
  static int metalOneStep_;
  static int metalThreeStep_;
  static int realNumTrackV_;
  static int realNumPTrackV_;
  static int verticalSubGrid_;
  static int gcdStep_;

  // Track related info
  static int numTrack_;
  static int numFin_;
  static int placementRow_;
  static float trackEachRow_;
  static int trackEachPRow_;
  static int numTrackH_;
  static int numTrackV_;
  static int numMetalLayer_;
  static int numPTrackH_;
  static int numPTrackV_;

  static int lastIdxPMOS_;

  static int numInstance_;

  static int numNets_org_;

  // Cell related info
  static int minWidth_;

  // ### PIN variables
  static std::vector<Pin *> pins;
  // (hashed) pin related instance name (or ext net) + (_S/G/D/A/B/Y) to net id
  // h_pin_id
  static std::map<unsigned int, int> h_InstPin_to_netID;
  // (hashed) instance name to first pin of this inst index inside pins. From
  // this start index and #finger, iterate all possible pins
  // h_pin_idx
  static std::map<unsigned int, int> h_instID_to_pinStart;
  // (hashed) pin name to index inside pins
  // h_pinId_idx
  static std::map<unsigned int, int> h_pinName_to_idx;
  // output pins to idx in pins
  static std::map<unsigned int, int> h_outpinId_idx;
  static std::map<unsigned int, std::string> h_pin_net;

  // ### NET variables
  static std::vector<Net *> nets;
  static std::map<int, int> h_extnets;
  // h_idx
  static std::map<unsigned int, int> h_netId_to_netIdx; // net ID to idx in nets
  static std::map<unsigned int, int> h_outnets;         // not used anywhere

  // ### INSTANCE variables
  static std::vector<Instance *> insts;
  static std::map<unsigned int, int> h_inst_idx;

  // ### Power Net/Pin Info
  // pinName to 1
  static std::map<unsigned int, int> h_pin_power;
  static std::map<unsigned int, int> h_net_power;

  // ### Partition Info
  static std::vector<std::tuple<std::string, std::string, int>>
      inst_partition;                         // not used for now
  static std::map<int, int> h_inst_partition; // not used for now
  static std::vector<std::tuple<int, std::vector<int>, int>>
      inst_partition_p; // not used for now
  static std::vector<std::tuple<int, std::vector<int>, int>>
      inst_partition_n;                        // not used for now
  static std::map<int, std::string> h_sdbInst; // not used for now

  // ### Crostalk Mitigation Info
  static std::map<std::string, int> h_net_track; // not used for now
  // static std::map<int, int> h_net_track_n;
  static std::map<int, std::vector<std::string>> h_track_net;
  // static std::map<int, int> h_net_track_t; // not used for now
  static std::map<int, std::string> h_net_opt;

  // ### Graph Variable
  static std::map<Triplet, Vertex *> vertices;
  static std::vector<UdEdge *> udEdges;
  static std::vector<Triplet *> boundaryVertices;
  static std::vector<OuterPin *> outerPins;
  static std::vector<Triplet *> leftCorners;
  static std::vector<Triplet *> rightCorners;
  static std::vector<Triplet *> frontCorners;
  static std::vector<Triplet *> backCorners;
  static std::map<std::string, Source *> sources;
  static std::map<std::string, Sink *> sinks;
  // static std::vector<Triplet *> subNodes;
  static std::vector<VirtualEdge *> virtualEdges;
  static std::map<std::string, std::vector<int>> edge_in;
  static std::map<std::string, std::vector<int>> edge_out;
  static std::map<std::string, std::vector<int>> vedge_in;
  static std::map<std::string, std::vector<int>> vedge_out;

  // Super Outer Node Keyword
  static std::string keySON;
};
