package controller;

import controller.utente.AggiungiAiPrefServlet;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import model.wishList.WishList;
import jakarta.servlet.http.*;
import jakarta.servlet.ServletException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class AggiungiAiPrefServletTest {

    private AggiungiAiPrefServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private LibroDAO mockLibroDAO;

    @BeforeEach
    void setUp() {
        // Inizializziamo la servlet
        servletUnderTest = new AggiungiAiPrefServlet();
        
        // Mock the DAO
        mockLibroDAO = mock(LibroDAO.class);
        servletUnderTest.setLibroDAO(mockLibroDAO);

        // Creiamo i mock
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);

        // Ogni volta che chiamo request.getSession() voglio che mi ritorni il mock session
        when(request.getSession()).thenReturn(session);
    }

    /**
     * SCENARIO PRINCIPALE / MAIN SCENARIO:
     * 1) Utente è loggato -> "cliente registrato"
     * 2) Clicca sull’icona per aggiungere un libro -> param "isbn"
     * 3) Il sistema aggiunge il libro alla wishlist -> JSON con "isInWishList" = true
     */
    @Test
    void testDoGet_SuccessAddBook() throws ServletException, IOException {
        // 1) Prepariamo i parametri
        String isbn = "9788804664567";
        when(request.getParameter("isbn")).thenReturn(isbn);
        
        // Mock the libro returned by DAO
        Libro mockLibro = new Libro();
        mockLibro.setIsbn(isbn);
        when(mockLibroDAO.doRetrieveById(isbn)).thenReturn(mockLibro);

        // 2) Simuliamo utente loggato in sessione
        Utente utente = new Utente();
        utente.setEmail("ciao4@gmail.com");
        utente.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(utente);

        // 3) La WishList in session è inizialmente vuota
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<Libro>());
        when(session.getAttribute("wishList")).thenReturn(wishList);

        // 4) Stiamo restituendo un JSON come response, quindi simuliamo l'output writer
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // 5) Eseguiamo la servlet
        servletUnderTest.doGet(request, response);

        // 6) Verifichiamo che il libro è stato aggiunto nella wishlist
        assertEquals(1, wishList.getLibri().size(),
                "La wishlist deve contenere esattamente 1 libro");

        Libro added = wishList.getLibri().get(0);
        assertEquals("9788804664567", added.getIsbn(),
                "L'ISBN del libro aggiunto deve corrispondere a quello inviato");

        // 7) Verifichiamo il contenuto JSON della risposta
        pw.flush();
        String jsonResponse = sw.toString();
        // Ci aspettiamo { "isInWishList": true }
        assertTrue(jsonResponse.contains("\"isInWishList\":true"),
                "La risposta JSON deve contenere isInWishList = true");
    }

    /**
     * SCENARIO ALTERNATIVO 2.a1:
     * - Utente non loggato -> reindirizzamento a 401 Unauthorized
     */
    @Test
    void testDoGet_UserNotLoggedIn() throws ServletException, IOException {
        // 1) Nessun utente in session
        when(session.getAttribute("utente")).thenReturn(null);

        // 2) Eseguiamo la servlet
        servletUnderTest.doGet(request, response);

        // 3) Verifichiamo che la servlet invoca sendError(401)
        verify(response).sendError(HttpServletResponse.SC_UNAUTHORIZED, "User not logged in");

        // 4) Verifichiamo che NON scrive nulla sul writer
        verify(response, never()).getWriter();
    }

    /**
     * SCENARIO ALTERNATIVO 2.b1:
     * - Il libro è già presente in wishlist -> il sistema lo rimuove
     */
    @Test
    void testDoGet_BookAlreadyInWishlist() throws ServletException, IOException {
        // 1) Prepariamo i parametri
        String isbn = "9788804664567";
        when(request.getParameter("isbn")).thenReturn(isbn);
        
        // Mock the libro returned by DAO
        Libro mockLibro = new Libro();
        mockLibro.setIsbn(isbn);
        when(mockLibroDAO.doRetrieveById(isbn)).thenReturn(mockLibro);

        // 2) Simuliamo utente loggato
        Utente utente = new Utente();
        utente.setEmail("ciao4@gmail.com");
        utente.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(utente);

        // 3) WishList contiene già il libro
        WishList wishList = new WishList();
        Libro libroEsistente = new Libro();
        libroEsistente.setIsbn(isbn);
        wishList.setLibri(new ArrayList<Libro>(java.util.List.of(libroEsistente)));
        when(session.getAttribute("wishList")).thenReturn(wishList);

        // 4) Simuliamo writer
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // 5) Eseguiamo la servlet
        servletUnderTest.doGet(request, response);

        // 6) Verifichiamo che ora la wishlist è vuota (il libro è stato rimosso)
        assertFalse(wishList.getLibri().contains(libroEsistente), "La wishlist non deve contenere il vecchio libro dopo la rimozione");

        // 7) JSON di risposta con "isInWishList": false
        pw.flush();
        String jsonResponse = sw.toString();
        assertTrue(jsonResponse.contains("\"isInWishList\":false"),
                "La risposta JSON deve contenere isInWishList = false");
    }

}