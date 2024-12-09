package br.com.chess.game.boardgame;
import java.util.Arrays;

public abstract class Piece {
    //@ spec_public
    //@ nullable
    protected Position position;
    //@ spec_public
    private Board board;

    /*@ public normal_behavior
      @     ensures this.board == board;
      @     ensures this.position == null;
      @ pure
      @*/
    public Piece(Board board) {
        this.board = board;
        position = null;
    }

    /*@ public normal_behavior
      @     ensures \result == this.board;
      @ pure
      @*/
    public Board getBoard() {
        return board;
    }

    /*@ ensures \result.length == board.getRows();
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @         \result[i] != null && \result[i].length == board.getColumns());
      @ pure
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ requires position.getRow() >= 0 && position.getRow() < board.getRows();
      @ requires position.getColumn() >= 0 && position.getColumn() < board.getColumns();
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
