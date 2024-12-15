package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.utils.Color;

public class Pawn extends ChessPiece {

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
    public Pawn(Board board, Color color, ChessMatch chessMatch) {
        super(board, color);
        this.chessMatch = chessMatch;
    }

    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat= new boolean[getBoard().getRows()][getBoard().getColumns()];
        Position p = new Position(0,0);

        if(position == null || !getBoard().positionExists(position)) {
            return mat;
        }

        //@ assert position.getColumn() + maxMove <= Integer.MAX_VALUE;
        //@ assert position.getRow() + maxMove <= Integer.MAX_VALUE;

//
//        if (getColor() == Color.WHITE) {
//            p.setValues(position.getRow() - 1, position.getColumn());
//            if (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() - 2, position.getColumn());
//            Position p2 = new Position(position.getRow() - 1, position.getColumn());
//            if (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p) && getBoard().positionExists(p2) && !getBoard().thereIsAPiece(p2) && getMoveCount() == 0){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() - 1, position.getColumn() - 1);
//            if (getBoard().positionExists(p) && isThereOpponentPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() - 1, position.getColumn() + 1);
//            if (getBoard().positionExists(p) && isThereOpponentPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            // #specialmove en passant white
//            if (position.getRow() == 3) {
//                Position left = new Position(position.getRow(), position.getColumn() - 1);
//                if (getBoard().positionExists(left) && isThereOpponentPiece(left) && getBoard().piece(left) == chessMatch.getEnPassantVulnerable()) {
//                    mat[left.getRow() - 1][left.getColumn()] = true;
//                }
//                Position right = new Position(position.getRow(), position.getColumn() + 1);
//                if (getBoard().positionExists(right) && isThereOpponentPiece(right) && getBoard().piece(right) == chessMatch.getEnPassantVulnerable()) {
//                    mat[right.getRow() - 1][right.getColumn()] = true;
//                }
//            }
//        }
//        else {
//            p.setValues(position.getRow() + 1, position.getColumn());
//            if (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() + 2, position.getColumn());
//            Position p2 = new Position(position.getRow() + 1, position.getColumn());
//            if (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p) && getBoard().positionExists(p2) && !getBoard().thereIsAPiece(p2) && getMoveCount() == 0){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() + 1, position.getColumn() + 1);
//            if (getBoard().positionExists(p) && isThereOpponentPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            p.setValues(position.getRow() + 1, position.getColumn() - 1);
//            if (getBoard().positionExists(p) && isThereOpponentPiece(p)){
//                mat[p.getRow()][p.getColumn()] = true;
//            }
//            // #specialmove en passant black
//            if (position.getRow() == 4) {
//                Position left = new Position(position.getRow(), position.getColumn() - 1);
//                if (getBoard().positionExists(left) && isThereOpponentPiece(left) && getBoard().piece(left) == chessMatch.getEnPassantVulnerable()) {
//                    mat[left.getRow() + 1][left.getColumn()] = true;
//                }
//                Position right = new Position(position.getRow(), position.getColumn() + 1);
//                if (getBoard().positionExists(right) && isThereOpponentPiece(right) && getBoard().piece(right) == chessMatch.getEnPassantVulnerable()) {
//                    mat[right.getRow() + 1][right.getColumn()] = true;
//                }
//            }
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

     /*@ also
       @ public normal_behavior
       @     ensures \result.equals("P");
       @ pure
       @*/
    @Override
    public String getString(){
        return "P";
    }
}
