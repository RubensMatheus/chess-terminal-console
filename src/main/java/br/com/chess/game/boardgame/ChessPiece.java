package br.com.chess.game.boardgame;
import br.com.chess.game.chess.ChessPosition;
import br.com.chess.game.chess.utils.Color;
import br.com.chess.game.pieces.Rook;

public abstract class ChessPiece {

    protected  /*@ nullable */ Position position; //@ in modelPosition;
    private Board board; //@ in modelBoard;

    private final Color color; //@ in modelColor;
    private int moveCount; //@ in modelCount;

    //@ public model Color modelColor;
    //@ private represents modelColor = this.color;

    //@ public model int modelCount;
    //@ private represents modelCount = this.moveCount;

    //@ public model int maxMove;

    //@ public model /*@ nullable */ Position modelPosition;
    //@ private represents modelPosition = this.position;

    //@ public model Board modelBoard;
    //@ private represents modelBoard = this.board;

    /*@ public normal_behavior
      @     ensures modelBoard == board;
      @     ensures modelPosition == null;
      @     ensures modelColor == color;
      @     ensures modelCount == 0;
      @ pure
      @*/
    public ChessPiece(Board board, Color color) {
        this.board = board;
        position = null;
        this.color = color;
        this.moveCount = 0;
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
      @ requires modelPosition.row >= 0 && modelPosition.row < modelBoard.rows;
      @ requires modelPosition.column >= 0 && modelPosition.column < modelBoard.columns;
      @ ensures \result.length == 8;
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @             \result[i].length == 8);
      @ also
      @ requires modelPosition == null ||
      @ !(modelPosition.row >= 0 && modelPosition.row < modelBoard.rows && modelPosition.column >= 0 && modelPosition.column < modelBoard.columns);
      @ ensures \result.length == 8;
      @ ensures (\forall int i; 0 <= i && i < \result.length;
      @             \result[i].length == 8);
      @ ensures (\forall int i, j;
      @         0 <= i && i < 8 &&
      @         0 <= j && j < 8;
      @         \result[i][j] == false);
      @ pure
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ requires modelPosition != null;
      @ requires modelPosition.row >= 0 && modelPosition.row < modelBoard.rows;
      @ requires modelPosition.column >= 0 && modelPosition.column < modelBoard.columns;
      @ requires position.getRow() >= 0 && position.getRow() < modelBoard.rows;
      @ requires position.getColumn() >= 0 && position.getColumn() < modelBoard.columns;
      @ also
      @ requires modelPosition == null ||
      @ !(modelPosition.row >= 0 && modelPosition.row < modelBoard.rows && modelPosition.column >= 0 && modelPosition.column < modelBoard.columns) ||
      @ !(position.getRow() >= 0 && position.getRow() < modelBoard.rows && position.getColumn() >= 0 && position.getColumn() < modelBoard.columns);
      @ ensures \result == false;
      @ pure
      @*/
    public boolean possibleMove(Position position) {
        if(this.position == null || !board.positionExists(this.position) || !board.positionExists(position)) {
            return false;
        }

        return possibleMoves()[position.getRow()][position.getColumn()];
    }

    /*@ requires modelPosition != null;
      @ requires modelPosition.row >= 0 && modelPosition.row < modelBoard.rows;
      @ requires modelPosition.column >= 0 && modelPosition.column < modelBoard.columns;
      @ also
      @ requires modelPosition == null ||
      @ !(modelPosition.row >= 0 && modelPosition.row < modelBoard.rows && modelPosition.column >= 0 && modelPosition.column < modelBoard.columns);
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

    /*@ public normal_behavior
      @     ensures \result == modelColor;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @     ensures \result == modelCount;
      @ pure
      @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @     requires modelCount < Integer.MAX_VALUE;
      @     ensures modelCount == \old(modelCount) + 1;
      @ assigns modelCount;
      @*/
    public void increaseMoveCount(){
        moveCount++;
    }

    /*@ public normal_behavior
      @     requires modelCount > Integer.MIN_VALUE;
      @     ensures modelCount == \old(modelCount) - 1;
      @ assigns modelCount;
      @*/
    public void decreaseMoveCount(){
        moveCount--;
    }


    /*@ public normal_behavior
      @     requires position.getRow() >= 0 && position.getColumn() >= 0;
      @     requires position.getRow() < modelBoard.rows && position.getColumn() < modelBoard.columns;
      @     requires modelBoard.pieces[position.getRow()][position.getColumn()] == null;
      @     ensures \result == false;
      @ also
      @ public normal_behavior
      @     requires position.getRow() >= 0 && position.getColumn() >= 0;
      @     requires position.getRow() < modelBoard.rows && position.getColumn() < modelBoard.columns;
      @     requires modelBoard.pieces[position.getRow()][position.getColumn()] != null;
      @     ensures \result == ((modelBoard.pieces[position.getRow()][position.getColumn()]).modelColor != this.modelColor);
      @ pure
      @*/
    public boolean isThereOpponentPiece(Position position) {
        /*@ nullable*/ ChessPiece piece = getBoard().piece(position);
        if (piece == null) {
            return false;
        }
        return piece.getColor() != getColor();
    }

    /*@ public normal_behavior
      @     requires modelPosition != null;
      @     requires modelPosition.getRow() >= 0 && modelPosition.getRow() <= 7;
      @     requires modelPosition.getColumn() >= 0 && modelPosition.getColumn() <= 7;
      @     ensures \result != null;
      @     ensures \result.getRow() == 8 - modelPosition.getRow();
      @     ensures \result.getColumn() == (char) ('a' + modelPosition.getColumn());
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires modelPosition == null || (modelPosition.getRow() < 0 || modelPosition.getRow() > 7
      @           || modelPosition.getColumn() < 0 || modelPosition.getColumn() > 7);
      @     ensures \result == null;
      @     assignable \nothing;
      @*/
    public /*@ nullable*/ ChessPosition getChessPosition(){
        return ChessPosition.fromPosition(position);
    }

    //@ pure
    public abstract String getString();
}
