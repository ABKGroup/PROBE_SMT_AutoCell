#pragma once
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

/*
    Contains Data Structures used for writting out constraints
*/


class Graph {
  public:
  void init_vertices();
  void init_udedges();
  void init_boundaryVertices(bool EXT_Parameter);
  void init_source(bool SON);
  void init_outerPins();
  void init_pinSON(bool SON);
  void init_corner();
  void init_virtualEdges();
  void init_edgeIn();
  void init_edgeOut();
  void init_edgeInOut();
  void init_vedgeInOut();

  // M_#_#
  void init_metal_var();
  // N#_E_#_#
  void init_net_edge_var();
  // N#_C#_E_#_#
  void init_net_commodity_edge_var();

  void init_extensible_boundary(int boundaryCondition);
};

// Integer Triplets for Vertex Class
// Example:
//  Triplet temp_vertex = {metal, row, col};
struct Triplet {
  bool valid_;
  int metal_;
  int row_;
  int col_;

  // null constructor
  Triplet() { 
    metal_ = -1;
    row_ = -1;
    col_ = -1;
    valid_ = false; 
  }

  // valid constructor
  Triplet(int metal, int row, int col) {
    metal_ = metal;
    row_ = row;
    col_ = col;
    valid_ = true;
  }

  // deconstructor
  ~Triplet() {}

  void setRow(int row) { row_ = row; }
  
  void setCol(int col) { col_ = col; }

  bool ifValid() {
    return (metal_ > 0 && row_ >= 0 && col_ >= 0);
  }

  bool operator==(const Triplet &rhs) const {
    // if (!valid_) { return false; }
    return metal_ == rhs.metal_ && row_ == rhs.row_ && col_ == rhs.col_;
  }

  bool operator<(const Triplet &rhs) const {
    // if (!valid_) { return false; }
    if (metal_ != rhs.metal_) {
      return metal_ < rhs.metal_;
    }

    if (row_ != rhs.row_) {
      return row_ < rhs.row_;
    }

    return col_ < rhs.col_;
  }

  std::string getVname() const {
    if (!valid_) {
      return "null";
    }
    return "m" + std::to_string(metal_) + "r" + std::to_string(row_) + "c" +
           std::to_string(col_);
  }

  void dump() const {
    if (!valid_) {
      std::cout << "[INFO] Null Vertex\n";
    }
    std::cout << "m" + std::to_string(metal_) + "r" + std::to_string(row_) +
                     "c" + std::to_string(col_)
              << std::endl;
  }
};

class Vertex {
  /*
    Virtual Graph Components: Vertex
  */
public:
  Vertex(int vIndex, Triplet *vCoord, std::vector<Triplet *> vADJ);

  int getVIndex() const { return vIndex_; }
  std::string getVName() const { return (*vCoord_).getVname(); }
  int getMetal() const { return vCoord_->metal_; }
  int getRow() const { return vCoord_->row_; }
  int getCol() const { return vCoord_->col_; }

  // Getter function for adjacent vertices
  Triplet *getLeftADJ() { return vADJ_[0]; }

  Triplet *getRightADJ() { return vADJ_[1]; }

  Triplet *getFrontADJ() const { return vADJ_[2]; }

  Triplet *getBackADJ() const { return vADJ_[3]; }

  Triplet *getUpADJ() const { return vADJ_[4]; }

  Triplet *getDownADJ() const { return vADJ_[5]; }

  Triplet *getFrontLeftADJ() const { return vADJ_[6]; }

  Triplet *getFrontRightADJ() const { return vADJ_[7]; }

  Triplet *getBackLeftADJ() const { return vADJ_[8]; }

  Triplet *getBackRightADJ() const { return vADJ_[9]; }

  void dump();

  // Hash Function
  static uint64_t hash(uint16_t metal, uint16_t row, uint16_t col);

private:
  int vIndex_;
  Triplet *vCoord_;
  std::vector<Triplet *> vADJ_;
};

class UdEdge {
  /*
    Virtual Graph Components: Undirected Edges
  */
public:
  UdEdge(int udEdgeIndex, Triplet *udEdgeTerm1, Triplet *udEdgeTerm2, int mCost,
         int wCost);
  int getUdEdgeIndex() const { return udEdgeIndex_; }
  Triplet *getUdFromEdge() const { return udEdgeTerm1_; }
  Triplet *getUdToEdge() const { return udEdgeTerm2_; }
  int getMCost() const { return mCost_; }
  int getWCost() const { return wCost_; }
  void dump();

private:
  int udEdgeIndex_;
  Triplet *udEdgeTerm1_;
  Triplet *udEdgeTerm2_;
  int mCost_;
  int wCost_;
};

class OuterPin {
  /*
    Output Pins
  */
public:
  OuterPin(std::string pinName, std::string netID, int commodityInfo);

  std::string getPinName() const { return pinName_; }
  std::string getNetID() const { return netID_; }
  int getCommodityInfo() const { return commodityInfo_; }
  void dump();

private:
  std::string pinName_;
  std::string netID_;
  int commodityInfo_;
};

class Source {
  /*
    Net Source
  */
public:
  Source(std::string netID, int numSubNodes,
         std::vector<Triplet*> boundaryVertices);

  std::string getNetID() const { return netID_; }
  int getNumSubNodes() const { return numSubNodes_; }
  Triplet* getBoundaryVertices(int idx) const {
    return boundaryVertices_[idx];
  }
  void dump();

private:
  std::string netID_;
  int numSubNodes_;
  std::vector<Triplet*> boundaryVertices_;
};

class Sink {
  /*
    Net Sink
  */
public:
  Sink(std::string netID, int numSubNodes,
       std::vector<Triplet*> boundaryVertices);

  std::string getNetID() const { return netID_; }
  int getNumSubNodes() const { return numSubNodes_; }
  Triplet* getBoundaryVertices(int idx) const {
    return boundaryVertices_[idx];
  }
  void dump();

private:
  std::string netID_;
  int numSubNodes_;
  std::vector<Triplet*> boundaryVertices_;
};

class VirtualEdge {
  /*
    Virtual Graph Components: Virtual Edges
  */
public:
  VirtualEdge(int vEdgeIndex, Triplet* vCoord, std::string pinName,
              int virtualCost);

  int getVEdgeIndex() const { return vEdgeIndex_; }
  Triplet* getVCoord() const { return vCoord_; }
  std::string getVName() const { return vCoord_->getVname(); }
  std::string getPinName() const { return pinName_; }
  int getVirtualCost() const { return virtualCost_; }
  void dump();

private:
  int vEdgeIndex_;
  Triplet* vCoord_;
  std::string pinName_;
  int virtualCost_;
};