#define FMT_HEADER_ONLY
#include "graph.hpp"
#include "SMTCell.hpp"
#include "dbConfig.hpp"
#include <fmt/core.h>
#include <fmt/format.h>

void Graph::init_vertices() {
  // ### VERTEX Generation
  // ### VERTEX Variables
  // std::map<Triplet, Vertex *> vertices;
  int vIndex = 0;
  int step = 0;
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }

    // fmt::print("numTrackH: {}, realNumTrackV: {}, step: {}\n",
    //            SMTCell::getNumTrackH(), SMTCell::getRealNumTrackV(), step);
    for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
      for (int col = 0; col < SMTCell::getRealNumTrackV(); col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }

        std::vector<Triplet *> tmp_vADJ;
        Triplet *vL_p, *vR_p, *vF_p, *vB_p, *vU_p, *vD_p, *vFL_p, *vFR_p,
            *vBL_p, *vBR_p; // ptrs to struct

        Triplet *tmp_coord_p =
            new Triplet(metal, row, col); // a ptr to tmp coordinate

        // ### Left Vertex
        if (col == 0) {
          vL_p = new Triplet();
        } else {
          int tmp_col = col - step;
          // get to the nearest track
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col -= step;
          }
          vL_p = new Triplet(metal, row, tmp_col);
        }

        // ### Right Vertex
        if (col == SMTCell::getRealNumTrackV() - 1) {
          vR_p = new Triplet();
        } else {
          int tmp_col = col + step;

          // prevent out of bound
          if (tmp_col > SMTCell::getRealNumTrackV() - 1) {
            continue;
          }
          // get to the nearest track
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col += step;
          }
          vR_p = new Triplet(metal, row, tmp_col);
        }

        // ### Front Vertex
        if (row == 0) {
          vF_p = new Triplet();
        } else {
          // int tmp_row = row - 1;
          vF_p = new Triplet(metal, row - 1, col);
        }

        // ### Back Vertex
        if (row == SMTCell::getLastRowIdx()) {
          vB_p = new Triplet();
        } else {
          // int tmp_row = row + 1;
          vB_p = new Triplet(metal, row + 1, col);
        }

        // ### Up Vertex
        if (metal == SMTCell::getNumMetalLayer()) {
          vU_p = new Triplet();
        } else {
          // int tmp_metal = metal + 1;
          vU_p = new Triplet(metal + 1, row, col);
        }

        // ### Down Vertex
        if (metal == 1) {
          vD_p = new Triplet();
        } else {
          // int tmp_metal = metal - 1;
          vD_p = new Triplet(metal - 1, row, col);
        }

        // ### FL Vertex
        if (row == 0 || col == 0) {
          vFL_p = new Triplet();
        } else {
          // int tmp_row = row - 1;
          // int tmp_col = col - 1;
          int tmp_col = col - step;
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col -= step;
          }

          vFL_p = new Triplet(metal, row - 1, tmp_col);
        }

        // ### FR Vertex
        if (row == 0 || col == SMTCell::getRealNumTrackV() - 1) {
          vFR_p = new Triplet();
        } else {
          int tmp_col = col + step;
          if (tmp_col > SMTCell::getRealNumTrackV() - 1) {
            continue;
          }
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col += step;
          }
          vFR_p = new Triplet(metal, row - 1, tmp_col);
        }

        // ### BL Vertex
        if (row == SMTCell::getLastRowIdx() || col == 0) {
          vBL_p = new Triplet();
        } else {
          int tmp_col = col - step;
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col -= step;
          }
          vBL_p = new Triplet(metal, row + 1, tmp_col);
        }

        // ### BR Vertex
        if (row == SMTCell::getLastRowIdx() ||
            col == SMTCell::getRealNumTrackV() - 1) {
          vBR_p = new Triplet();
        } else {
          int tmp_col = col + step;
          if (tmp_col > SMTCell::getRealNumTrackV() - 1) {
            continue;
          }
          while (tmp_col % SMTCell::getMetalOneStep() != 0 &&
                 tmp_col % SMTCell::getMetalThreeStep() != 0) {
            tmp_col += step;
          }
          vBR_p = new Triplet(metal, row + 1, tmp_col);
        }

        tmp_vADJ = {vL_p, vR_p,  vF_p,  vB_p,  vU_p,
                    vD_p, vFL_p, vFR_p, vBL_p, vBR_p};

        SMTCell::addVertex((*tmp_coord_p),
                           new Vertex(vIndex, tmp_coord_p, tmp_vADJ));
        vIndex++;
      }
    }
  }
}

void Graph::init_udedges() {
  // ### UNDIRECTED EDGE Generation
  // ### UNDIRECTED EDGE Variables
  int udEdgeIndex = 0;
  int udEdgeNumber = -1;
  int vCost = 4;
  int mCost = 1;
  int vCost_1 = 4;
  int mCost_1 = 1;
  int vCost_34 = 4;
  int mCost_4 = 1;
  int wCost = 1;

  int step;

  // ### DATA STRUCTURE:  UNDIRECTED_EDGE [index] [Term1] [Term2]
  // [mCost] [wCost] # Odd Layers: Vertical Direction   Even Layers:
  // Horizontal Direction
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        Triplet *udEdgeTerm1_p = new Triplet(metal, row, col);

        // check if the vertex is valid
        if (!SMTCell::ifVertex((*udEdgeTerm1_p))) {
          continue;
        }

        Triplet *udEdgeTerm2_p;
        // # Even Layers ==> Horizontal
        if (metal % 2 == 0) {
          // # Right Edge
          udEdgeTerm2_p = SMTCell::getVertex((*udEdgeTerm1_p))->getRightADJ();
          if (udEdgeTerm2_p->ifValid()) {
            if (metal == 4) {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, mCost_4, wCost));
            } else {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, mCost, wCost));
            }
            udEdgeIndex++;
          }
          // # Up Edge
          udEdgeTerm2_p = SMTCell::getVertex((*udEdgeTerm1_p))->getUpADJ();
          if (udEdgeTerm2_p->ifValid()) {
            if (col % SMTCell::getMetalThreeStep() == 0) {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, vCost, vCost));
              udEdgeIndex++;
            }
          }
        } else { // # Odd Layers ==> Vertical
          // This does not mean that the vertex is on SD column!!!
          if (metal == 3 && col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }

          // # Back Edge
          udEdgeTerm2_p = SMTCell::getVertex((*udEdgeTerm1_p))->getBackADJ();
          if (udEdgeTerm2_p->ifValid()) {
            if (metal == 3) {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, mCost, wCost));
            } else {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, mCost_1, wCost));
            }
            udEdgeIndex++;
          }

          // # Up Edge
          udEdgeTerm2_p = SMTCell::getVertex((*udEdgeTerm1_p))->getUpADJ();
          if (udEdgeTerm2_p->ifValid()) {
            if (metal == 1) {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, vCost_1, vCost));

              udEdgeIndex++;
            } else {
              SMTCell::addUdEdge(new UdEdge(udEdgeIndex, udEdgeTerm1_p,
                                            udEdgeTerm2_p, vCost_34, vCost));
              udEdgeIndex++;
            }
          }
        }
      }
    }
  }
}

void Graph::init_source(bool SON) {
  std::vector<Triplet *> tmp_subNodes;
  int numSubNodes;
  int numSources;
  int outerPinFlagSource = 0;
  int outerPinFlagSink = 0;
  std::string keyValue;

  for (int i = 0; i < SMTCell::getPinCnt(); i++) {
    tmp_subNodes.clear();
    if (SMTCell::getPin(i)->getPinIO() == "s") { // source
      if (SMTCell::getPin(i)->getPinLength() == -1) {
        if (SON == 1) {
          if (outerPinFlagSource == 0) {
            // copy boundary vertices from begin to end
            // subNodes.assign(boundaryVertices.begin(),
            // boundaryVertices.end());
            tmp_subNodes = SMTCell::copyBoundaryVertex();
            outerPinFlagSource = 1;
            keyValue = SMTCell::getKeySON();
          } else {
            continue;
          }
        } else { // SON Disable
                 // copy boundary vertices from begin to end
          // subNodes.assign(boundaryVertices.begin(), boundaryVertices.end());
          // SMTCell::addBoundaryVerticesToSubNode();
          tmp_subNodes = SMTCell::copyBoundaryVertex();
          keyValue = SMTCell::getPin(i)->getPinName();
        }
      } else {
        for (int j = 0; j < SMTCell::getPin(i)->getPinLength(); j++) {
          tmp_subNodes.push_back(
              new Triplet(1, SMTCell::getPin(i)->getPinYpos()[j],
                          SMTCell::getPin(i)->getPinXpos()));
          // SMTCell::addSubNode(new Triplet(1,
          // SMTCell::getPin(i)->getPinYpos()[j],
          //                                SMTCell::getPin(i)->getPinXpos()));
        }
        keyValue = SMTCell::getPin(i)->getPinName();
      }
      numSubNodes = tmp_subNodes.size();

      // Outer Pin should be at last in
      // the input File Format
      // [2018-10-15]
      // sources[keyValue] =
      //     new Source(SMTCell::getPin(i)->getNetID(), numSubNodes,
      //     tmp_subNodes);

      SMTCell::addSource(keyValue, new Source(SMTCell::getPin(i)->getNetID(),
                                              numSubNodes, tmp_subNodes));
    } else if (SMTCell::getPin(i)->getPinIO() == "t") { // sink
      if (SMTCell::getPin(i)->getPinLength() == -1) {
        if (SON == 1) {
          if (outerPinFlagSink == 0) {
            // copy boundary vertices from begin to end
            // subNodes.assign(boundaryVertices.begin(),
            // boundaryVertices.end()); SMTCell::addBoundaryVerticesToSubNode();
            tmp_subNodes = SMTCell::copyBoundaryVertex();
            outerPinFlagSink = 1;
            keyValue = SMTCell::getKeySON();
          } else {
            continue;
          }
        } else {
          // copy boundary vertices from begin to end
          // subNodes.assign(boundaryVertices.begin(), boundaryVertices.end());
          // SMTCell::addBoundaryVerticesToSubNode();
          tmp_subNodes = SMTCell::copyBoundaryVertex();
          keyValue = SMTCell::getPin(i)->getPinName();
        }
      } else {
        for (int j = 0; j < SMTCell::getPin(i)->getPinLength(); j++) {
          tmp_subNodes.push_back(
              new Triplet(1, SMTCell::getPin(i)->getPinYpos()[j],
                          SMTCell::getPin(i)->getPinXpos()));
          // SMTCell::addSubNode(new Triplet(1,
          // SMTCell::getPin(i)->getPinYpos()[j],
          //                                SMTCell::getPin(i)->getPinXpos()));
        }
        keyValue = SMTCell::getPin(i)->getPinName();
      }
      numSubNodes = tmp_subNodes.size();

      // sinks[keyValue] =
      //     new Sink(SMTCell::getPin(i)->getNetID(), numSubNodes,
      //     tmp_subNodes);
      SMTCell::addSink(keyValue, new Sink(SMTCell::getPin(i)->getNetID(),
                                          numSubNodes, tmp_subNodes));
    }
  }
}

void Graph::init_boundaryVertices(bool EXT_Parameter) {
  int numBoundaries = 0;
  int step = 0;
  // ### Normal External Pins - Top&top-1 layer only
  for (int metal = SMTCell::getNumMetalLayer() - 1;
       metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        if (metal % 2 == 0) {
          continue;
        }
        if (EXT_Parameter == 0) {
          if (row == 1 || row == SMTCell::getNumTrackH() - 4) {

            SMTCell::addBoundaryVertex(new Triplet(metal, row, col));
          }
        } else {
          SMTCell::addBoundaryVertex(new Triplet(metal, row, col));
        }
      }
    }
  }
}

void Graph::init_outerPins() {
  // std::map<std::string, int> h_outerPin;    // not used
  // int numOuterPins = 0;
  int commodityInfo = -1;

  // this needs to migrate to SMTCell
  for (int i = 0; i < SMTCell::getPinCnt(); i++) {
    Pin *p = SMTCell::getPin(i);
    if (p->getPinLength() == -1) {
      // # Initializing
      commodityInfo = -1;
      // # Find Commodity Infomation
      for (int j = 0; j < SMTCell::getNetCnt(); j++) {
        Net *n = SMTCell::getNet(j);
        if (n->getNetName() == p->getNetID()) {
          for (int sinkIndexofNet = 0; sinkIndexofNet < n->getNumSinks();
               sinkIndexofNet++) {
            // std::cout << sinkIndexofNet << std::endl;
            if (n->getSinks_inNet(sinkIndexofNet) == p->getPinName()) {
              commodityInfo = sinkIndexofNet;
            }
          }
        }
      }

      if (commodityInfo == -1) {
        std::cerr << "ERROR: Cannot Find the commodity "
                     "Information!!\n\n";
      }

      SMTCell::addOuterPin(
          new OuterPin(p->getPinName(), p->getNetID(), commodityInfo));
      // h_outerPin[p->getPinName()] = 1;
    }
  }
}

void Graph::init_corner() {
  // ### (LEFT | RIGHT | FRONT | BACK) CORNER VERTICES Generation
  // # At the top-most metal layer, only vias exist.
  int step = 0;
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
      for (int col = 0; col < SMTCell::getRealNumTrackV(); col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }

        if (metal == 1 && col % (2 * step) != 0) {
          continue;
        }

        Triplet *cornerVertex = new Triplet(metal, row, col);

        if (col == 0) {
          SMTCell::addLeftCorner(cornerVertex);
        }

        if (col == SMTCell::getRealNumTrackV() - 1) {
          SMTCell::addRightCorner(cornerVertex);
        } else if (col < SMTCell::getRealNumTrackV() - 1 &&
                   col > SMTCell::getRealNumTrackV() - 1 -
                             SMTCell::getMetalThreeStep() &&
                   metal >= 3) {
          SMTCell::addRightCorner(cornerVertex);
        }

        if (row == 0) {
          SMTCell::addFrontCorner(cornerVertex);
        }

        if (row == SMTCell::getLastRowIdx()) {
          SMTCell::addBackCorner(cornerVertex);
        }
      }
    }
  }
}

void Graph::init_pinSON(bool SON) {
  if (SON == 1) {
    // Pin Information
    // Modification
    for (int pinIndex = 0; pinIndex < SMTCell::getPinCnt(); pinIndex++) {
      for (int outerPinIndex = 0; outerPinIndex < SMTCell::getOuterPinCnt();
           outerPinIndex++) {
        if (SMTCell::getPin(pinIndex)->getPinName() ==
            SMTCell::getOuterPin(outerPinIndex)->getPinName()) {
          // partition flag
          SMTCell::getPin(pinIndex)->setPinName(Pin::keySON);
          SMTCell::getPin(pinIndex)->setNetID("Multi");
          continue;
        }
      }
    }
    // SON Node should be
    // last elements to use
    // pop
    int SONFlag = 0;
    int tmp_cnt = SMTCell::getPinCnt();
    Pin *pin;
    for (int i = 0; i <= tmp_cnt; i++) {
      if (SMTCell::getPin(tmp_cnt - i)->getPinName() == Pin::keySON) {
        SONFlag = 1;
        pin = SMTCell::popLastPin();
      }
    }
    if (SONFlag == 1) {
      // partition flag
      SMTCell::addPin(pin);
    }
  }

  // Net Information
  // Modification from Outer
  // pin to "SON"
  if (SON == 1) {
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int sinkIndex = 0;
           sinkIndex < SMTCell::getNet(netIndex)->getNumSinks(); sinkIndex++) {
        for (int outerPinIndex = 0; outerPinIndex < SMTCell::getOuterPinCnt();
             outerPinIndex++) {
          if (SMTCell::getNet(netIndex)->getSinks_inNet(sinkIndex) ==
              SMTCell::getOuterPin(outerPinIndex)->getPinName()) {
            SMTCell::getNet(netIndex)->setSinks_inNet(sinkIndex, Pin::keySON);
            continue;
          }
        }
      }
      for (int pinIndex = 0;
           pinIndex < SMTCell::getNet(netIndex)->getN_pinNets(); pinIndex++) {
        for (int outerPinIndex = 0; outerPinIndex < SMTCell::getOuterPinCnt();
             outerPinIndex++) {
          if (SMTCell::getNet(netIndex)->getPins_inNet(pinIndex) ==
              SMTCell::getOuterPin(outerPinIndex)->getPinName()) {
            SMTCell::getNet(netIndex)->setPins_inNet(pinIndex, Pin::keySON);
            continue;
          }
        }
      }
    }
  }
}

void Graph::init_virtualEdges() {
  int vEdgeIndex = 0;
  int vEdgeNumber = 0;
  int virtualCost = 0;
  int step = 0;

  for (int pinIdx = 0; pinIdx < SMTCell::getPinCnt(); pinIdx++) {
    if (SMTCell::getPin(pinIdx)->getPinIO() == "s") { // source
      if (SMTCell::ifSource(SMTCell::getPin(pinIdx)->getPinName())) {
        if (SMTCell::ifInst(SMTCell::getPin(pinIdx)->getInstID())) {
          std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getPinInst(pinIdx)->getInstWidth(),
              SMTCell::getTrackEachPRow());

          if (SMTCell::ifPinInstPMOS(pinIdx)) {
            int ru = SMTCell::getRoutingTrack(
                SMTCell::getNumPTrackH() - 1 -
                SMTCell::getConnection(
                    SMTCell::getPinInst(pinIdx)->getInstWidth() /
                    tmp_finger[0]));
            int rl = SMTCell::getRoutingTrack(SMTCell::getNumPTrackH() - 1);

            for (int row = 0;
                 row <= floor(SMTCell::getNumTrackH() / 2 + 0.5) - 2; row++) {
              for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
                   col += SMTCell::getMetalOneStep()) {
                if (SMTCell::findTrack(row) && row <= ru && row >= rl) {
                  // ROW  | 1 | 2 | 3 | 4 | 5 |
                  // PIN  | S | G | D | G | S |
                  // Gate Pin should be connected to even column
                  if (SMTCell::getPin(pinIdx)->getPinType() == "G" &&
                      SMTCell::ifSDCol(col)) {
                    continue;
                  } 
                  // Source or Drain Pin should be connected to odd column
                  else if (SMTCell::getPin(pinIdx)->getPinType() != "G" &&
                             SMTCell::ifGCol(col)) {
                    continue;
                  }

                  SMTCell::addVirtualEdge(new VirtualEdge(
                      vEdgeIndex, new Triplet(1, row, col),
                      SMTCell::getPin(pinIdx)->getPinName(), virtualCost));

                  vEdgeIndex++;
                }
              }
            }
          } else {
            int ru = SMTCell::getRoutingTrack(0);
            int rl = SMTCell::getRoutingTrack(SMTCell::getConnection(
                SMTCell::getPinInst(pinIdx)->getInstWidth() / tmp_finger[0]));
            for (int row = floor(SMTCell::getNumTrackH() / 2 + 0.5) - 1;
                 row <= SMTCell::getNumTrackH() - 3; row++) {
              for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
                   col += SMTCell::getMetalOneStep()) {
                if (SMTCell::findTrack(row) && row <= ru && row >= rl) {
                  // ROW  | 1 | 2 | 3 | 4 | 5 |
                  // PIN  | S | G | D | G | S |
                  // Gate Pin should be connected to even column
                  if (SMTCell::getPin(pinIdx)->getPinType() == "G" &&
                      SMTCell::ifSDCol(col)) {
                    continue;
                  } 
                  // Source or Drain Pin should be connected to odd column
                  else if (SMTCell::getPin(pinIdx)->getPinType() != "G" &&
                             SMTCell::ifGCol(col)) {
                    continue;
                  }

                  SMTCell::addVirtualEdge(new VirtualEdge(
                      vEdgeIndex, new Triplet(1, row, col),
                      SMTCell::getPin(pinIdx)->getPinName(), virtualCost));

                  vEdgeIndex++;
                }
              }
            }
          }
        } else {
          std::cerr << "[ERROR] Virtual Edge Generation : Instance Information "
                       "not found!!"
                    << std::endl;
          exit(-1);
        }
      }
    } else if (SMTCell::getPin(pinIdx)->getPinIO() == "t") { // sink
      if (SMTCell::getSink(SMTCell::getPin(pinIdx)->getPinName())) {
        if (SMTCell::getPin(pinIdx)->getPinName() == SMTCell::getKeySON()) {
          for (int term = 0;
               term < SMTCell::getSink(SMTCell::getPin(pinIdx)->getPinName())
                          ->getNumSubNodes();
               ++term) {

            SMTCell::addVirtualEdge(new VirtualEdge(
                vEdgeIndex,
                SMTCell::getSink(SMTCell::getPin(pinIdx)->getPinName())
                    ->getBoundaryVertices(term),
                SMTCell::getPin(pinIdx)->getPinName(), virtualCost));
            vEdgeIndex++;
          }
        } else if (SMTCell::ifPinInst(pinIdx)) {
          std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getPinInst(pinIdx)->getInstWidth(),
              SMTCell::getTrackEachPRow());

          if (SMTCell::ifPinInstPMOS(pinIdx)) {
            int ru = SMTCell::getRoutingTrack(
                SMTCell::getNumPTrackH() - 1 -
                SMTCell::getConnection(
                    SMTCell::getPinInst(pinIdx)->getInstWidth() /
                    tmp_finger[0]));
            int rl = SMTCell::getRoutingTrack(SMTCell::getNumPTrackH() - 1);

            for (int row = 0;
                 row <= floor(SMTCell::getNumTrackH() / 2 + 0.5) - 2; row++) {
              for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
                   col += SMTCell::getMetalOneStep()) {
                if (SMTCell::findTrack(row) && row <= ru && row >= rl) {
                  if (SMTCell::getPin(pinIdx)->getPinType() == "G" &&
                      SMTCell::ifSDCol(col)) {
                    continue;
                  } else if (SMTCell::getPin(pinIdx)->getPinType() != "G" &&
                             SMTCell::ifGCol(col)) {
                    continue;
                  }

                  SMTCell::addVirtualEdge(new VirtualEdge(
                      vEdgeIndex, new Triplet(1, row, col),
                      SMTCell::getPin(pinIdx)->getPinName(), virtualCost));
                  vEdgeIndex++;
                }
              }
            }
          } else {
            int ru = SMTCell::getRoutingTrack(0);
            int rl = SMTCell::getRoutingTrack(SMTCell::getConnection(
                SMTCell::getPinInst(pinIdx)->getInstWidth() / tmp_finger[0]));

            for (int row = floor(SMTCell::getNumTrackH() / 2 + 0.5) - 1;
                 row <= SMTCell::getNumTrackH() - 3; row++) {
              for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
                   col += SMTCell::getMetalOneStep()) {
                if (SMTCell::findTrack(row) && row <= ru && row >= rl) {
                  if (SMTCell::getPin(pinIdx)->getPinType() == "G" &&
                      SMTCell::ifSDCol(col)) {
                    continue;
                  } else if (SMTCell::getPin(pinIdx)->getPinType() != "G" &&
                             SMTCell::ifGCol(col)) {
                    continue;
                  }

                  SMTCell::addVirtualEdge(new VirtualEdge(
                      vEdgeIndex, new Triplet(1, row, col),
                      SMTCell::getPin(pinIdx)->getPinName(), virtualCost));
                  vEdgeIndex++;
                }
              }
            }
          }
        } else {
          std::cerr << "[ERROR] Virtual Edge Generation : Instance Information "
                       "not found!!\n";
          exit(-1);
        }
      }
    }
  }
}

void Graph::init_edgeInOut() {
  for (int i = 0; i < SMTCell::getUdEdgeCnt(); i++) {
    // from
    SMTCell::addEdgeOut(SMTCell::getUdEdge(i)->getUdFromEdge()->getVname(), i);
    // to
    SMTCell::addEdgeIn(SMTCell::getUdEdge(i)->getUdToEdge()->getVname(), i);
  }
}

void Graph::init_vedgeInOut() {
  for (int i = 0; i < SMTCell::getVirtualEdgeCnt(); i++) {
    SMTCell::addVEdgeOut(SMTCell::getVirtualEdge(i)->getVName(), i);
    SMTCell::addVEdgeIn(SMTCell::getVirtualEdge(i)->getPinName(), i);
  }
}

void Graph::init_metal_var() {
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
    int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
    int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
    int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
    if (SMTCell::ifSDCol(fromCol) || SMTCell::ifSDCol(toCol)) {
      if (fromMetal == 1 && toMetal == 1) {
        std::string variable_name = fmt::format(
            "M_{}_{}",
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
        SMTCell::assignTrueVar(variable_name, 0, false);
      }
    }
  }
}

void Graph::init_net_edge_var() {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
         udEdgeIndex++) {
      int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
      int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
      int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
      int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
      int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
      int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
      if (SMTCell::ifSDCol(fromCol) || SMTCell::ifSDCol(toCol)) {
        if (fromMetal == 1 && toMetal == 1) {
          std::string variable_name = fmt::format(
              "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
          SMTCell::assignTrueVar(variable_name, 0, false);
        }
      }
    }
  }
}

void Graph::init_net_commodity_edge_var() {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
        int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
        int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
        int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
        if (SMTCell::ifSDCol(fromCol) || SMTCell::ifSDCol(toCol)) {
          if (fromMetal == 1 && toMetal == 1) {
            std::string variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex,
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
                SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
            SMTCell::assignFalseVar(variable_name);
          }
        }
      }
    }
  }
}

void Graph::init_extensible_boundary(int boundaryCondition) {
  if (boundaryCondition == 1) {
    // do nothing
  } else {
    for (int leftVertex = 0; leftVertex < SMTCell::getLeftCornerCnt();
         leftVertex++) {
      int metal = SMTCell::getLeftCorner(leftVertex)->metal_;
      if (metal % 2 == 0) {
        std::string variable_name = fmt::format(
            "M_LeftEnd_{}", SMTCell::getLeftCorner(leftVertex)->getVname());
        SMTCell::assignTrueVar(variable_name, 0, false);
      }
    }

    for (int rightVertex = 0; rightVertex < SMTCell::getRightCornerCnt();
         rightVertex++) {
      int metal = SMTCell::getRightCorner(rightVertex)->metal_;
      if (metal % 2 == 0) {
        std::string variable_name = fmt::format(
            "M_{}_RightEnd", SMTCell::getRightCorner(rightVertex)->getVname());
        SMTCell::assignTrueVar(variable_name, 0, false);
      }
    }

    for (int frontVertex = 0; frontVertex < SMTCell::getFrontCornerCnt();
         frontVertex++) {
      int metal = SMTCell::getFrontCorner(frontVertex)->metal_;
      if (metal % 2 == 1) {
        std::string variable_name = fmt::format(
            "M_FrontEnd_{}", SMTCell::getFrontCorner(frontVertex)->getVname());
        SMTCell::assignTrueVar(variable_name, 0, false);
      }
    }

    for (int backVertex = 0; backVertex < SMTCell::getBackCornerCnt();
         backVertex++) {
      int metal = SMTCell::getBackCorner(backVertex)->metal_;
      if (metal % 2 == 1) {
        std::string variable_name = fmt::format(
            "M_{}_BackEnd", SMTCell::getBackCorner(backVertex)->getVname());
        SMTCell::assignTrueVar(variable_name, 0, false);
      }
    }
  }
}

Vertex::Vertex(int vIndex, Triplet *vCoord, std::vector<Triplet *> vADJ) {
  vIndex_ = vIndex;
  vCoord_ = vCoord;
  vADJ_ = vADJ;
}

uint64_t Vertex::hash(uint16_t metal, uint16_t row, uint16_t col) {
  uint64_t key = (uint64_t)metal << 32;
  key = key | (uint64_t)row << 16;
  key = key | (uint64_t)col;
  return key;
}

// debug
void Vertex::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", vIndex_);
  fmt::print("  {},\n", vCoord_->getVname());
  fmt::print("  [\n");
  for (auto i : vADJ_)
    fmt::print("    {},\n", i->getVname());
  fmt::print("  ]\n");
  fmt::print("]\n");
}

UdEdge::UdEdge(int udEdgeIndex, Triplet *udEdgeTerm1, Triplet *udEdgeTerm2,
               int mCost, int wCost) {
  udEdgeIndex_ = udEdgeIndex;
  udEdgeTerm1_ = udEdgeTerm1;
  udEdgeTerm2_ = udEdgeTerm2;
  mCost_ = mCost;
  wCost_ = wCost;
}

// debug
void UdEdge::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", udEdgeIndex_);
  fmt::print("  '{}',\n", udEdgeTerm1_->getVname());
  fmt::print("  '{}',\n", udEdgeTerm2_->getVname());
  fmt::print("  {},\n", mCost_);
  fmt::print("  {}\n", wCost_);
  fmt::print("]\n");
}

OuterPin::OuterPin(std::string pinName, std::string netID, int commodityInfo) {
  pinName_ = pinName;
  netID_ = netID;
  commodityInfo_ = commodityInfo;
}

// debug
void OuterPin::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", pinName_);
  fmt::print("  {},\n", netID_);
  fmt::print("  {},\n", commodityInfo_);
  fmt::print("]\n");
}

Source::Source(std::string netID, int numSubNodes,
               std::vector<Triplet *> boundaryVertices) {
  netID_ = netID;
  numSubNodes_ = numSubNodes;
  boundaryVertices_ = boundaryVertices;
}

// debug
void Source::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", netID_);
  fmt::print("  {},\n", numSubNodes_);
  fmt::print("  [\n");
  for (auto bv : boundaryVertices_)
    fmt::print("  {},\n", bv->getVname());
  fmt::print("  ]\n");
  fmt::print("]\n");
}

Sink::Sink(std::string netID, int numSubNodes,
           std::vector<Triplet *> boundaryVertices) {
  netID_ = netID;
  numSubNodes_ = numSubNodes;
  boundaryVertices_ = boundaryVertices;
}

// debug
void Sink::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", netID_);
  fmt::print("  {},\n", numSubNodes_);
  fmt::print("  [\n");
  for (auto bv : boundaryVertices_)
    fmt::print("  {},\n", bv->getVname());
  fmt::print("  ]\n");
  fmt::print("]\n");
}

VirtualEdge::VirtualEdge(int vEdgeIndex, Triplet *vCoord, std::string pinName,
                         int virtualCost) {
  vEdgeIndex_ = vEdgeIndex;
  vCoord_ = vCoord;
  pinName_ = pinName;
  virtualCost_ = virtualCost;
}

// debug
void VirtualEdge::dump() {
  fmt::print("[\n");
  fmt::print("  {},\n", vEdgeIndex_);
  fmt::print("  {},\n", vCoord_->getVname());
  fmt::print("  {},\n", pinName_);
  fmt::print("  {},\n", virtualCost_);
  fmt::print("]\n");
}