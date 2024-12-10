package br.com.chess.game.boardgame;
import java.util.Arrays;

public abstract class Piece {

    protected /*@ nullable */ Position position; //@ in modelPosition;
    private Board board; //@ in modelBoard;


    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = this.position;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = this.board;

    /*@ public normal_behavior
      @     ensures modelBoard == board;
      @     ensures modelPosition == null;
      @ pure
      @*/
    public Piece(Board board) {
        this.board = board;
        position = null;
    }

    /*@ public normal_behavior
      @     ensures \result == modelBoard;
      @ pure
      @*/
    public Board getBoard() {
        return board;
    }

    /*@ public normal_behavior
      @     ensures \result == modelPosition;
      @ pure
      @*/
    public /*@ nullable */ Position getPosition() {
        return position;
    }


    /*@ ensures \result.length == modelBoard.getRows();
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @         \result[i] != null && \result[i].length == modelBoard.getColumns());
      @ pure
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ requires position.getRow() >= 0 && position.getRow() < modelBoard.getRows();
      @ requires position.getColumn() >= 0 && position.getColumn() < modelBoard.getColumns();
      @ pure
      @*/
    public boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }

    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (int i=0; i<mat.length; i++) {
            for (int j=0; j< mat[i].length; j++) {
                if (mat[i][j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
