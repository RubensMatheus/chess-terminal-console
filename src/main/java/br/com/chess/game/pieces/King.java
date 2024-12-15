package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.utils.Color;

public class King extends ChessPiece {

    private ChessMatch chessMatch; //@ in modelMatch;

    //@ public represents maxMove = 2;

    //@ public model ChessMatch modelMatch;
    //@ private represents modelMatch = this.chessMatch;

    /*@ public normal_behavior
      @     ensures modelMatch == chessMatch;
      @     ensures modelBoard == board;
      @     ensures modelColor == color;
      @ pure
      @*/
    public King(Board board, Color color, ChessMatch chessMatch) {
        super(board, color);
        this.chessMatch = chessMatch;
    }

    /*@ public normal_behavior
      @     ensures \result == modelMatch;
      @ pure
      @*/
    public ChessMatch getChessMatch() {
        return chessMatch;
    }

    /*@ also
      @ public normal_behavior
      @     ensures \result.equals("R");
      @ pure
      @*/
    @Override
    public String getString(){
        return "R";
    }

//    /*@ skipesc */
//    private boolean canMove(Position position){
//        ChessPiece p = getBoard().piece(position);
//        return  p == null || p.getColor() != getColor();
//    }
//
//    /*@ skipesc */
//    private boolean testRookCastling(Position position){
//        ChessPiece p = getBoard().piece(position);
//        return position !=null && p instanceof Rook && getColor() == getColor() && p.getMoveCount() == 0;
//    }

    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat= new boolean[getBoard().getRows()][getBoard().getColumns()];

        if(position == null || !getBoard().positionExists(position)) {
            return mat;
        }

        //@ assert position.getColumn() + maxMove <= Integer.MAX_VALUE;
        //@ assert position.getRow() + maxMove <= Integer.MAX_VALUE;

//        Position p = new Position(0,0);
//
//        //above
//        p.setValues(position.getRow() - 1, position.getColumn());
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//        //below
//        p.setValues(position.getRow() + 1, position.getColumn());
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//        //left
//        p.setValues(position.getRow(), position.getColumn() - 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//        //right
//        p.setValues(position.getRow(), position.getColumn() + 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//
//        p.setValues(position.getRow() - 1, position.getColumn() - 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//
//        p.setValues(position.getRow() + 1, position.getColumn() + 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//
//        p.setValues(position.getRow() + 1, position.getColumn() - 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//
//        //southeast
//        p.setValues(position.getRow() - 1, position.getColumn() + 1);
//        if(getBoard().positionExists(p) && canMove(p)){
//            mat[p.getRow()][p.getColumn()] = true;
//        }
//
//
//        //Special move castling
//        if(getMoveCount() == 0 && !chessMatch.isCheck()){
//            //# special move castling kingside rook
//            Position positionT1 = new Position(position.getRow(), position.getColumn() + 3);
//            if(testRookCastling(positionT1)){
//                Position p1 = new Position(position.getRow(), position.getColumn() + 1);
//                Position p2 = new Position(position.getRow(), position.getColumn() + 2);
//                if(getBoard().piece(p1) == null && getBoard().piece(p2) == null){
//                    mat[position.getRow()][position.getColumn() + 2] = true;
//                }
//            }
//            //# special move castling queenside rook
//            Position positionT2 = new Position(position.getRow(), position.getColumn() - 4);
//            if(testRookCastling(positionT2)){
//                Position p1 = new Position(position.getRow(), position.getColumn() - 1);
//                Position p2 = new Position(position.getRow(), position.getColumn() - 2);
//                Position p3 = new Position(position.getRow(), position.getColumn() - 3);
//                if(getBoard().piece(p1) == null && getBoard().piece(p2) == null && getBoard().piece(p3) == null){
//                    mat[position.getRow()][position.getColumn() - 2] = true;
//                }
//            }
//
//        }


        //@ assume mat.length == getBoard().getRows();
        //@ assume (\forall int i; 0 <= i && i < mat.length;
        //@         mat[i] != null && mat[i].length == getBoard().getColumns());
        //@ assume (\forall int x, y;
        //@         0 <= x && x < mat.length && 0 <= y && y < mat[x].length;
        //@         mat[x][y] ==> (getBoard().positionExistsBasic(x, y) &&
        //@                        (getBoard().pieces[x][y] == null ||
        //@                         getBoard().pieces[x][y].getColor() != this.getColor())));
        return mat;
    }


}