package br.com.chess.game.boardgame;
import br.com.chess.game.chess.ChessPiece;

public abstract class Piece {

    protected /*@ nullable */ Position position; //@ in modelPosition;
    private Board board; //@ in modelBoard;

    //@ public model int maxMove;

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

    /*@ requires modelPosition != null;
      @ requires getBoard().positionExists(modelPosition);
      @ requires modelPosition.getRow() + maxMove <= Integer.MAX_VALUE;
      @ requires modelPosition.getColumn() + maxMove <= Integer.MAX_VALUE;
      @ ensures \result.length == modelBoard.getRows();
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @             \result[i].length == modelBoard.getColumns());
      @ pure
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ requires modelPosition != null;
      @ requires getBoard().positionExists(modelPosition);
      @ requires modelPosition.getRow() + maxMove <= Integer.MAX_VALUE;
      @ requires modelPosition.getColumn() + maxMove <= Integer.MAX_VALUE;
      @ requires position.getRow() >= 0 && position.getRow() < modelBoard.getRows();
      @ requires position.getColumn() >= 0 && position.getColumn() < modelBoard.getColumns();
      @ pure
      @*/
    public boolean possibleMove(Position position) {
        return possibleMoves()[position.getRow()][position.getColumn()];
    }

    /*@ requires modelPosition != null;
      @ requires getBoard().positionExists(modelPosition);
      @ requires modelPosition.getRow() + maxMove <= Integer.MAX_VALUE;
      @ requires modelPosition.getColumn() + maxMove <= Integer.MAX_VALUE;
      @ pure
      @*/
    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();

        /*@ maintaining 0 <= i && i <= mat.length;
          @ maintaining (\forall int k, l;
          @     0 <= k && k < i && 0 <= l && l < mat[k].length;
          @     !mat[k][l]);
          @ decreasing mat.length - i;
          @*/
        for (int i = 0; i < mat.length; i++) {
            /*@ maintaining 0 <= j && j <= mat[i].length;
              @ maintaining (\forall int l;
              @     0 <= l && l < j; !mat[i][l]);
              @ decreasing mat[i].length - j;
              @*/
            for (int j = 0; j < mat[i].length; j++) {
                if (mat[i][j]) {
                    /*@ assert (\exists int k, l;
                      @     0 <= k && k < mat.length && 0 <= l && l < mat[k].length;
                      @     mat[k][l]);
                      @*/
                    return true;
                }
            }
        }
        return false;
    }

}
