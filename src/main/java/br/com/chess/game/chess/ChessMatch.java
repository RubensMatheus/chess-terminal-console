package br.com.chess.game.chess;

import br.com.chess.game.boardgame.*;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;
import br.com.chess.game.pieces.*;

import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
/*@ skipesc */
public class ChessMatch {
    private ChessPiece enPassantVulnerable;
    private ChessPiece promoted;
    private Board board;
    private Integer turn;
    private Color currentPlayer;
    private boolean check;
    private boolean checkMate;

    private List<ChessPiece> piecesOnTheBoard = new ArrayList<>();
    private List<ChessPiece> capturedChessPieces = new ArrayList<>();

    public Integer getTurn() {
        return turn;
    }

    public Color getCurrentPlayer() {
        return currentPlayer;
    }

    public boolean isCheck() {
        return check;
    }

    public boolean isCheckMate() {
        return checkMate;
    }

    public ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    public ChessPiece getPromoted() {
        return promoted;
    }

    public ChessMatch() {
        this.board = new Board(8, 8);
        turn = 1;
        currentPlayer = Color.WHITE;
        initialSetup();
    }

    /*@ skipesc */
    public ChessPiece[][] getChessPieces() {
        ChessPiece[][] mat = new ChessPiece[board.getRows()][board.getColumns()];
        for (int i = 0; i < board.getRows(); i++) {
            for (int j = 0; j < board.getColumns(); j++) {
                mat[i][j] = (ChessPiece) board.piece(i, j);
            }
        }
        return mat;
    }



    /*@ skipesc */
    public ChessPiece performChessMove(ChessPosition sourcePosition, ChessPosition targetPosition) {
        Position source = sourcePosition.toPosition();
        Position target = targetPosition.toPosition();
        validateSourcePosition(source);
        validateTargetPosition(source, target);
        ChessPiece capturedChessPiece = makeMove(source, target);
        if (testCheck(currentPlayer)) {
            undoMove(source, target, capturedChessPiece);
            throw new ChessException("Você não pode se colocar em check");
        }
        ChessPiece movedChessPiece = (ChessPiece)board.piece(target);

        //#specialmove promotion
        promoted = null;
        if(movedChessPiece instanceof Pawn){
            if((movedChessPiece.getColor() == Color.WHITE && target.getRow() == 0 )||(movedChessPiece.getColor() == Color.BLACK && target.getRow() == 7 )){
                promoted =  (ChessPiece)board.piece(target);
                promoted = replacepromotedChessPiece("A");
            }
        }

        check = (testCheck(opponent(currentPlayer))) ? true : false;

        if (testCheckMate(opponent(currentPlayer))) {
            checkMate = true;
        } else {
            nextTurn();
        }

        // #specialmove en passant
        if (movedChessPiece instanceof Pawn && (target.getRow() == source.getRow() - 2 || target.getRow() == source.getRow() + 2)) {
            enPassantVulnerable = movedChessPiece;
        }
        else {
            enPassantVulnerable = null;
        }

        return (ChessPiece) capturedChessPiece;
    }

    /*@ skipesc */
    public ChessPiece replacepromotedChessPiece(String type){
        if(promoted == null){
            throw new IllegalStateException("Não há peça para ser promovida");
        }
        if(!type.equals("T") && !type.equals("A") && !type.equals("C") && !type.equals("B")){
            throw new InvalidParameterException("Tipo invalido de promoção");
        }
        Position position = promoted.getChessPosition().toPosition();
        ChessPiece p = board.removeChessPiece(position);
        piecesOnTheBoard.remove(p);

        ChessPiece newChessPiece = newChessPiece(type, promoted.getColor());
        board.placeChessPiece(newChessPiece,position);
        piecesOnTheBoard.add(newChessPiece);

        return newChessPiece;
    }

    /*@ skipesc */
    private ChessPiece newChessPiece(String type, Color color) {
        if (type.equals("B")) return new Bishop(board, color);
        if (type.equals("C")) return new Knight(board, color);
        if (type.equals("A")) return new Queen(board, color);
        return new Rook(board, color);
    }

    /*@ skipesc */
    private void validateSourcePosition(Position position) {
        if (!board.thereIsAPiece(position)) {
            throw new ChessException("Não há nenhuma peça na posição de origem.");
        }
        if (currentPlayer != ((ChessPiece) board.piece(position)).getColor()) {
            throw new ChessException("A peça escolhida não é sua.");
        }
        if (!board.piece(position).isThereAnyPossibleMove()) {
            throw new ChessException("Não há movimentos possíveis para a peça escolhida");
        }
    }

    /*@ skipesc */
    public boolean[][] possibleMoves(ChessPosition sourcePosition) {
        Position position = sourcePosition.toPosition();
        validateSourcePosition(position);
        return board.piece(position).possibleMoves();
    }

    /*@ skipesc */
    private ChessPiece makeMove(Position source, Position target) {
        ChessPiece p = (ChessPiece) board.removeChessPiece(source);
        p.increaseMoveCount();
        ChessPiece capturedChessPiece = board.removeChessPiece(target);
        board.placeChessPiece(p, target);
        if (capturedChessPiece != null) {
            piecesOnTheBoard.remove(capturedChessPiece);
            capturedChessPieces.add(capturedChessPiece);
        }

        //#Special move castling king side rook
        if(p instanceof King && target.getColumn() == source.getColumn() + 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() + 3);
            Position targetT = new Position(source.getRow(), source.getColumn() + 1);
            ChessPiece rook =board.removeChessPiece(sourceT);
            board.placeChessPiece(rook,targetT);
            rook.increaseMoveCount();
        }
        //#Special move castling king side rook
        else if(p instanceof King && target.getColumn() == source.getColumn() - 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() - 4);
            Position targetT = new Position(source.getRow(), source.getColumn() - 1);
            ChessPiece rook =  board.removeChessPiece(sourceT);
            board.placeChessPiece(rook,targetT);
            rook.increaseMoveCount();
        }
        // #specialmove en passant
        if (p instanceof Pawn) {
            if (source.getColumn() != target.getColumn() && capturedChessPiece == null) {
                Position pawnPosition;
                if (p.getColor() == Color.WHITE) {
                    pawnPosition = new Position(target.getRow() + 1, target.getColumn());
                }
                else {
                    pawnPosition = new Position(target.getRow() - 1, target.getColumn());
                }
                capturedChessPiece = board.removeChessPiece(pawnPosition);
                capturedChessPieces.add(capturedChessPiece);
                piecesOnTheBoard.remove(capturedChessPiece);
            }
        }

        return capturedChessPiece;
    }

    /*@ skipesc */
    private void undoMove(Position source, Position target, ChessPiece captured) {
        ChessPiece p = (ChessPiece) board.removeChessPiece(target);
        p.decreaseMoveCount();
        board.placeChessPiece(p, source);

        if (captured != null) {
            board.placeChessPiece(captured, target);
            capturedChessPieces.remove(captured);
            piecesOnTheBoard.add(captured);
        }
        //#Special move castling king side rook
        if(p instanceof King && target.getColumn() == source.getColumn() + 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() + 3);
            Position targetT = new Position(source.getRow(), source.getColumn() + 1);
            ChessPiece rook = (ChessPiece)board.removeChessPiece(targetT);
            board.placeChessPiece(rook,sourceT);
            rook.decreaseMoveCount();
        }
        //#Special move castling king side rook
        else if(p instanceof King && target.getColumn() == source.getColumn() - 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() - 4);
            Position targetT = new Position(source.getRow(), source.getColumn() - 1);
            ChessPiece rook = (ChessPiece)board.removeChessPiece(targetT);
            board.placeChessPiece(rook,sourceT);
            rook.decreaseMoveCount();
        }

        // #specialmove en passant
        if (p instanceof Pawn) {
            if (source.getColumn() != target.getColumn() && captured == enPassantVulnerable) {
                ChessPiece pawn = (ChessPiece)board.removeChessPiece(target);
                Position pawnPosition;
                if (p.getColor() == Color.WHITE) {
                    pawnPosition = new Position(3, target.getColumn());
                }
                else {
                    pawnPosition = new Position(4, target.getColumn());
                }
                board.placeChessPiece(pawn, pawnPosition);
            }
        }
    }

    /*@ skipesc */
    private void validateTargetPosition(Position source, Position target) {
        if (!board.piece(source).possibleMove(target)) {
            throw new ChessException("A peça escolhida não pode se mover para a posição escolhida");
        }
    }

    /*@ skipesc */
    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ skipesc */
    private void placeNewChessPiece(char column, int row, ChessPiece piece) {
        board.placeChessPiece(piece, new ChessPosition(column, row).toPosition());
        piecesOnTheBoard.add(piece);
    }

    /*@ skipesc */
    private Color opponent(Color color) {
        return (color == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ skipesc */
    private ChessPiece king(Color color) {
        List<ChessPiece> list = listColorChessPieces(color);
        for (ChessPiece p : list) {
            if (p instanceof King) {
                return (ChessPiece) p;
            }
        }
        throw new IllegalStateException("Não existe um rei com a cor " + color);
    }

    /*@ skipesc */
    private List<ChessPiece> listColorChessPieces(Color color) {
        return piecesOnTheBoard.stream()
                .filter(x -> ((ChessPiece) x)
                        .getColor() == color)
                .collect(Collectors.toList());
    }

    /*@ skipesc */
    private boolean testCheck(Color color) {
        Position kingPosition = king(color).getChessPosition().toPosition();
        List<ChessPiece> opponentChessPieces = listColorChessPieces(opponent(color));

        for (ChessPiece p : opponentChessPieces) {
            boolean[][] mat = p.possibleMoves();
            if (mat[kingPosition.getRow()][kingPosition.getColumn()]) {
                return true;
            }
        }
        return false;
    }

    /*@ skipesc */
    private boolean testCheckMate(Color color) {
        if (!testCheck(color)) {
            return false;
        }
        List<ChessPiece> list = listColorChessPieces(color);
        for (ChessPiece p : list) {
            boolean[][] mat = p.possibleMoves();
            for (int i = 0; i < board.getRows(); i++) {
                for (int j = 0; j < board.getColumns(); j++) {
                    if (mat[i][j]) {
                        Position source = ((ChessPiece) p).getChessPosition().toPosition();
                        Position target = new Position(i, j);
                        ChessPiece capturedChessPiece = makeMove(source, target);
                        boolean testCheck = testCheck(color);
                        undoMove(source, target, capturedChessPiece);
                        if (!testCheck) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;

    }

    /*@ skipesc */
    private void initialSetup() {
        placeNewChessPiece('a', 1, new Rook(board, Color.WHITE));
        placeNewChessPiece('b', 1, new Knight(board, Color.WHITE));
        placeNewChessPiece('c', 1, new Bishop(board, Color.WHITE));
        placeNewChessPiece('d', 1, new Queen(board, Color.WHITE));
        placeNewChessPiece('e', 1, new King(board, Color.WHITE, this));
        placeNewChessPiece('f', 1, new Bishop(board, Color.WHITE));
        placeNewChessPiece('g', 1, new Knight(board, Color.WHITE));
        placeNewChessPiece('h', 1, new Rook(board, Color.WHITE));
        placeNewChessPiece('a', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('b', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('c', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('d', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('e', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('f', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('g', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('h', 2, new Pawn(board, Color.WHITE,this));

        placeNewChessPiece('a', 8, new Rook(board, Color.BLACK));
        placeNewChessPiece('b', 8, new Knight(board, Color.BLACK));
        placeNewChessPiece('c', 8, new Bishop(board, Color.BLACK));
        placeNewChessPiece('d', 8, new Queen(board, Color.BLACK));
        placeNewChessPiece('e', 8, new King(board, Color.BLACK, this));
        placeNewChessPiece('f', 8, new Bishop(board, Color.BLACK));
        placeNewChessPiece('g', 8, new Knight(board, Color.BLACK));
        placeNewChessPiece('h', 8, new Rook(board, Color.BLACK));
        placeNewChessPiece('a', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('b', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('c', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('d', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('e', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('f', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('g', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('h', 7, new Pawn(board, Color.BLACK,this));
    }
}
