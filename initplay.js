'use strict';


/* GAME RULES MODEL
  Sequentially indexing the squares of the chessboard
	left->right, bottom->top
	56 ... 63 rank 8
	48 ... 55 rank 7
	40 ... 47 .
	32 ... 39 .
	24 ... 31 .
	16 ... 23 rank 3
	 8 ... 15 rank 2
	 0 ...  7 rank 1		
	Each of these index numbers is log_2 of 
	the bit of that square on the chessboard.
*/

/**
 * 
 * @param {string} gamejson one or more Forsyth-Edwards Notation (FEN)
 * strings without fullmove number, concatenated with a string of chars
 * representing captured pieces, in FEN, arranged in an array as a game
 * history, therefore the array index i can be used to derive the 
 * fullmove number, i+1, and the array itself JSON.stringified.
 */
const Model = function(gamejson) {
  this.gamejson = gamejson;
}

/* Initial position FEN w/o fullmove number and trailing space as a
join to an empty initially captured list */
Model.INITFEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 ";

/**
 * 
 * @returns Static "initialPosition" is used to construct a new Model
 * object with initial position as the first history point. Serves as
 * a bean-like no-param constructor.
 */
Model.initialPosition = function() {
  return new Model(JSON.stringify([Model.INITFEN]));
}

/**
 * Derive bitboard from Forsyth-Edwards Notation (FEN) for chess positions
 * using most recent position.
 * Modified Forsyth-Edwards Notation (FEN) piece placement data (PPD)
 * as follows: 
    * ranks ascending instead of descending
    * rank delimiters removed
    * digits > 1 replaced by a string of 1s of length equal to digit
  Modified for the purpose of having the occupancy of all 64 squares
  on the chessboard specified by a single char and so that each piece
  FEN char's index in the string is the same as its square's log_2 on
  a bitboard.
  The most recent FEN from the game history JSON is used.
*/
Model.prototype.getBitboards = function() {
  const ppdSeq = JSON.parse(this.gamejson).at(-1).split(' ')[0].replace(
      /\d/g, (d) => '1'.repeat(d)).split('/').toReversed().join('');
  const foundPc = (pieceFEN) => (char) => char === pieceFEN ? 1 : 0;
  return "KQRBNPkqrbnp".split('').map(pieceFEN => {
    return BigInt('0b' + ppdSeq.split('').map(foundPc(pieceFEN)).join(''));
  });
};

/**
 * 
 * @returns Object with FEN chars for each type of piece bound to a csv
 * string of indices in the serialization of the board where a copy of
 * the piece may be found, except in case of kings, since there is only
 * one of each color king, where the value will be a number.
 */
Model.prototype.getGridPiecePlacement = function() {
  const bitboards = this.getBitboards();
  const toBin = (bitbd) => bitbd.toString(2);
  const msbIdx = (bin) => bin.length - 1;
  const placement = {};
  const keys = "KQRBNPkqrbnp";
  for (const key of keys) {
    if (key === 'K') {
      placement[key] = msbIdx(toBin(bitboards[0]));
    } else if (key === 'k') {
      placement[key] = msbIdx(toBin(bitboards[6]));
    } else {
      const bitbd = bitboards[keys.indexOf(key)];
      const bin = toBin(bitbd);
      const msb = msbIdx(bin);
      const toIdcs = (bit, idx) => 1 * bit ? (msb - idx) : null;
      const non0 = (arr) => arr.filter(v => v != null);
      placement[key] = non0(bin.split('').map(toIdcs)).join();
    }
  }
  return placement;
};

/**
 * 
 * @param {bigint} bigvalue 64-bit int where set bits indicate squares to mark
 * @returns csv of board serialization indices indicating which squares to mark
 */
Model.prototype.getGridMarksPlacement = function(bigvalue) {
  const bits = bigvalue.toString(2);
  const msb = bits.length - 1;
  const toIdcs = (bit, idx) => 1 * bit ? (msb - idx) : null;
  const non0 = (arr) => arr.filter(v => v != null);
  return non0(bits.split('').map(toIdcs)).join();
};

/**
 * 
 * @param {string} xy concatenated coordinates of 8x8 grid on [0,7]
 * @param {boolean} isForDefense set to analyze attacks on square x,y
 * @returns If not isForDefense, this method returns a csv of board
 * serialization indices indicating which squares to mark as pseudolegal moves.
 * If isForDefense is true, this method returns a stringified array of
 * information about each move as follows: if the piece on x,y can move in
 * N directions, the elems 0 - N-1 of array are moves in each direction
 * 1 square out, N to 2N-1 are moves in each direction 2 squares out, etc.;
 * nulls indicate out of bounds or collision with same color piece--unallowed
 * moves; if the move info is only a number that's a move to the empty square
 * indicated by serialized board grid index 0-63; if the move info is a csv
 * string then serialized board index of move is on the LHS of comma and
 * capturable/attacking piece RHS.
 */
Model.prototype.pseudolegal = function(xy, isForDefense = false) {
  const i0 = 1 * xy[0] + 8 * xy[1];
  const bitboards = this.getBitboards();
  const toBin = (bitbd) => bitbd.toString(2).padStart(64, 0);
  const indexOfPiece = (i) => bitboards.map(b => toBin(b)[i]).indexOf(1);
  /*
   * Option to use queen attack pattern as a way to detect
   * attacks on any square, occupied or empty */
  const idxOfPc0 = isForDefense && 1 || indexOfPiece(i0);
  //
  const curFEN = JSON.parse(this.gamejson).at(-1);
  const activeColor = curFEN.split(' ')[1];
  const idxToColor = (idxOfPc) => idxOfPc < 6 ? 'w' : 'b';
  const color0 = isForDefense && activeColor ||
      idxOfPc0 > -1 && idxToColor(idxOfPc0);

  if (color0 && color0 !== activeColor) {
    return '';
  }

  const byPiece = [
    (v, k) => k < 8 && v !== 0, // king,queen slide any direction
    (v, k) => k < 8 && v !== 0,
    (v, k) => k < 8 && k % 2 === 1, // rooks rank-n-file slide
    (v, k) => k < 8 && v !== 0 && k % 2 === 0, // bishops diags. slide
    (v, k) => k >= 8, // knights take jumps not slides
    (v, k) => (color0 === 'b') ? (k < 3) : (k > 5 && k < 8)
  ][idxOfPc0 % 6];

  const idxSteps = [
    -9, -8, -7, -1, 0, +1, +7, +8, +9, // slides
    -17, -15, -10, -6, +6, +10, +15, +17 // jumps
  ].filter(byPiece);

  const stopRules = (i, di) => {
    /* Pieces and already out-of-bounds: "i" value to change into next on 
     * ray is given not as a single number but a string combo of index and
     * pieceFEN, indicating attacking/capturable piece, beyond which no more
     * moves should be listed; "i" is null because we're out of bounds already
     * or there is a piece of same color at the "i" to change to next */
    if (i?.length || i == null) {
      return null;
    }
    /* Remaining cases: boundary conditions 
    */
    // bottom and top rank bounds
    if (i + di < 0 || i + di > 63) {
      return null;
    }
    // file 'a' modulo wrap to file 'h' not allowed
    if (i % 8 === 0) {
      return ((i + di) % 8 !== 7) ? (i + di) : null;
    }
    // file 'h' modulo wrap to file 'a' not allowed
    if (i % 8 === 7) {
      return ((i + di) % 8 > 0) ? (i + di) : null;
    }
    // additional loss of jumps for files a,b,g,h
    if ((i % 8 < 2 && (di === -10 || di === +6)) ||
        (i % 8 > 5 && (di === +10 || di === -6))) {
      return null;
    }
    // Lastly, for no pieces or BCs, just do the step calc.
    return i + di;
  };

  const pcCheck = (stepResult) => {
    if (stepResult === null) { // already out of bounds or past a piece
      return null;
    }
    const idxOfPc = indexOfPiece(stepResult);
    if (idxOfPc < 0) {
      return stepResult;
    }
    const destColor = idxToColor(stepResult);
    // capturable piece of opp. color (non-king)
    if (destColor !== color0 && idxOfPc > 0 && idxOfPc !== 6) { 
      return stepResult + ',' + "KQRBNPkqrbnp"[idxOfPc];
    }
    return null;  // same color as piece on origin
  };

  const out1 = idxSteps.map(di => pcCheck(stopRules(i0, di)));

  /* 
   * How to make a sum from the things in outs that aren't null,
   * also untangling csv strings representing captuer/attack spots */
  const sum2bitbd = (iValues) => {
    return iValues.filter(iValue => iValue != null).map(iValue => {
      if (typeof iValue === 'string') {
        return 1 * iValue.split(',')[0];
      }
      return iValue;
    }).reduce((sum, iValue) => sum + BigInt(2 ** iValue), 0n);
  };

  /*
   * handle king, knight, pawn, each with only 1 possible move per direction
   */
  // knights & kings
  if (idxOfPc0 % 6 === 4 || idxOfPc0 % 6 === 0) {
    return this.getGridMarksPlacement(sum2bitbd(out1));
  }
  // pawns white & black
  if (idxOfPc0 === 5 || idxOfPc0 === 11) {
    // NOTE no pawn out1 board ser. indices can ever be 0
    const eptsFEN = curFEN.split(' ')[3];
    const epts = eptsFEN !== '-' && "abcdefgh".indexOf(eptsFEN[0]) + 
        8 * (eptsFEN[1] - 1);
    const lcap = epts === out1[0] && out1[0] || typeof out1[0] === 'string' &&
        1 * out1[0].split(',')[0];
    const push = typeof out1[1] === 'number' && out1[1]; // always F or num > 0
    const rcap = epts === out1[2] && out1[2] || typeof out1[2] === 'string' &&
        1 * out1[2].split(',')[0];
    const isWhite = idxOfPc0 === 5;
    const dblpush = /* begin with init rank test */ (isWhite && (i0 < 16) ||
        !isWhite && (i0 >= 48)) && /* single push must be available */ push &&
            isWhite && (indexOfPiece(i0 + 16) < 0) && (i0 + 16) ||
                !isWhite && (indexOfPiece(i0 - 16) < 0) && (i0 - 16);
    const arr = (value) => value && [value] || [];
    return this.getGridMarksPlacement(sum2bitbd(
        arr(lcap).concat(arr(push)).concat(arr(rcap)).concat(arr(dblpush))));
  }

  /*
   * queen, rook, bishop, or attack analysis
   */
  const past1Step = (prevIdxResult, idxOfDirection) => {
    return pcCheck(stopRules(prevIdxResult, idxSteps[idxOfDirection]));
  };
  const out2 = out1.map(past1Step);
  const out3 = out2.map(past1Step);
  const out4 = out3.map(past1Step);
  const out5 = out4.map(past1Step);
  const out6 = out5.map(past1Step);
  const out7 = out6.map(past1Step);
  if (isForDefense) {
    return JSON.stringify([out1, out2, out3, out4, out5, out6, out7].flat());
  }
  return this.getGridMarksPlacement(
      sum2bitbd([out1, out2, out3, out4, out5, out6, out7].flat()));
};

/**
 * 
 * @param {string} xy 
 * @returns 
 */
Model.prototype.movegen = function(xy) {
  // find king of active color
  // run king's xy through pseudolegal with isfordefense=true
  // if king in check, only interposing and capture-of-single-attacker allowed
  // if double check... game over 0 moves?
  // if given xy IS king's, get king's pseudolegal
  // run each of king's pseudos back into pseudolegal gen w/ isfordef=treu
  // determine king castling moves if avail.
  // if xy not king, run pseudolegal
  // filter pseudolegals w/ interposing/capsingle if in check
};


/**
 * 
 * @param {string} seq expanded L-R B-T sequential piece placement
 * @returns FEN-format piece placement data
 */
Model.prototype.toFEN = function(seq) {
  return Array.from({length: 8}, function(v, k) {
    return seq.slice(k * 8, k * 8 + 8).replace(/1{2,}/g,
        (ones) => ones.length);
  }).toReversed().join('/');
};

Model.prototype.setBitboards = function(moveData) {
  const a = 1 * moveData[0] + 8 * moveData[1];
  const b = 1 * moveData[2] + 8 * moveData[3];
  const bitbds = this.bitboards;
  const idxOfMvPc = this.idxOfPiece(BigInt(2 ** a), bitbds);
  const idxOfTarg = this.idxOfPiece(BigInt(2 ** b), bitbds);
  const captured = idxOfTarg > -1 && this.FENCHARSEQ[idxOfTarg] || '';
  const modForMvPc = bitbds[idxOfMvPc] - BigInt(2 ** a) + BigInt(2 ** b);
  const modForCapt = idxOfTarg > -1 && bitbds[idxOfTarg] - BigInt(2 ** b);
  this.CAPTURES += captured;
  if (moveData === '4060') {;}
  const capBitbds = modForCapt && (bitbds.slice(0, idxOfTarg).concat(
      [modForCapt]).concat(bitbds.slice(idxOfTarg + 1)));
  const srcForNex = capBitbds && capBitbds || bitbds;
  const movBitbds = srcForNex.slice(0, idxOfMvPc).concat(
      [modForMvPc]).concat(srcForNex.slice(idxOfMvPc + 1));
  // make FEN from movbitbds:
  // take log2 of each bitboard, this is the index to put piecefen in expanded ppd
  this.gameJSON = JSON.stringify(JSON.parse(this.gameJSON).concat([]));
};




/* GAME VIEWS */

class View {
  constructor() {
    // To make a container for a single square of the chessboard
    const createSquare = () => document.createElement("DIV");

    // To make a set of containers, one for each square of the chessboard
    const containers = () => Array.from({length: 64}, createSquare);

    // Given index of rank (0-7) decide whether that rank's
    // left-to-right checkering begins with dark or lite shade.
    const checker = (i) => i % 2 && ['dark','lite'] || ['lite','dark'];

    // Create the set of checkered chessboard squares.
    this.squares = containers().map(function(div, idx) {
      // Select shade from rank's alternation pattern
      // by parity of the index of file (0-7).
      div.setAttribute("class", checker(Math.floor(idx / 8))[idx % 8 % 2]);
      return div;
    });

    this.board.append(...this.squares);
  }

  get board() {
    return document.getElementById("board");
  }

  set board(listenerParams) {
    this.board.addEventListener(...listenerParams);
  }

  /* CSS grid expects cells left->right but top->bottom.
   * The first 8 items in divs for grid container should get pieces
   * for bitboard indices 56-63, then, decreasing the mult. of 8 count,
   * the next 8 container divs get pieces for bitboard indices 48-55,
   * rank 7. So for each grid container index in the map sequence, 
   *  transform by the following formula */
  #seq(idx) {
    return 56 + idx % 8 - 8 * Math.floor(idx / 8);
  }

  // draw pieces on board
  renderPosition(bitboards) {
    // unicodes for the 12 physical chess pieces strung together
    const UNICODES = Array.from({length: 12}, function(v, k) {
      return String.fromCharCode(0x2654 + k);
    }).join('');

    const cssIndices = Array.from({length: 64}, (v, k) => k).map(this.#seq);

    this.squares.map(function(div, idx) {
      const pieceSearch = (b) => (b & BigInt(2 ** cssIndices[idx])) > 0n;
      const indexOfPiece = bitboards.map(pieceSearch).indexOf(true);
      const pieceCode = UNICODES[indexOfPiece] || '';
      div.textContent = pieceCode;
      return div;
    });
    return;
  }

  get bounds() {
    return this.board.getBoundingClientRect();
  }

  // mark squares due to a piece pick click
  renderMarks(moveGeneratorResult) {
    if (moveGeneratorResult == undefined) {
      this.squares.map(function(div) {
        div.textContent = div.textContent.replace('x', '');
        return div;
      });
      return;
    }
    if (moveGeneratorResult === 'no piece') {
      return;
    }
    const bitboard = moveGeneratorResult;
    const cssIndices = Array.from({length: 64}, (v, k) => k).map(this.#seq);
    this.squares.map(function(div, idx) {
      if ((bitboard & BigInt(2 ** cssIndices[idx])) > 0n) {
        div.textContent += 'x';
      }      
      return div;
    });
    return;
  }

  // bonus debug tool
  plotBits(big64b) {
    const formRanks = Array.from({length: 64}, function(v, k) {
      return (big64b & BigInt(2 ** k)) > 0 && 1 || 0;
    });
    const bitStr = Array.from({length: 8}, function(v, k) {
      return formRanks.slice(56 - k * 8, 64 - k * 8).join(' ');
    }).join('\n');
    console.log(bitStr);
    return;
  }
}




// GAME CONTROLLER

class Controller {
  #xyOfSelectedPiece;

  constructor(model, view) {
    this.model = model;
    this.view = view;
  }

  init() {
    this.view.board = [ "click", this.selectSquare.bind(this) ];
    this.view.renderPosition = this.view.renderPosition.bind(this.view);
    this.model.movegen = this.model.movegen.bind(this.model);
    this.view.renderPosition(this.model.bitboards);
  }

  selectSquare(e) {
    const { bottom, height, left, width } = this.view.bounds;
    const chessX = Math.floor((e.clientX - left) / Math.floor(width / 8));
    const chessY = Math.floor((bottom - e.clientY) / Math.floor(height / 8));
    /*
    if (this.#xyOfSelectedPiece) {
      this.view.renderMarks();
      this.model.bitboards = this.#xyOfSelectedPiece + chessX + chessY;
      this.view.renderPosition(this.model.bitboards);
      this.#xyOfSelectedPiece = undefined;
      return;
    }*/
    this.#xyOfSelectedPiece = `${chessX}` + chessY;
    this.view.renderMarks(this.model.movegen(this.#xyOfSelectedPiece));
    console.log(this.#xyOfSelectedPiece);
  }
}




const model = Model.initialPosition();
const view = new View();
const controller = new Controller(model, view);

controller.init();
