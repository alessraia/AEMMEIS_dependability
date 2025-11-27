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

        // 7) Verifichiamo che session.setAttribute è stata chiamata con la wishlist aggiornata
        verify(session).setAttribute("wishList", wishList);

        // 8) Verifichiamo che il content type sia stato impostato correttamente
        verify(response).setContentType("application/json");

        // 9) Verifichiamo il contenuto JSON della risposta
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

        // 7) Verifichiamo che session.setAttribute è stata chiamata
        verify(session).setAttribute("wishList", wishList);

        // 8) Verifichiamo che il content type sia stato impostato
        verify(response).setContentType("application/json");

        // 9) JSON di risposta con "isInWishList": false
        pw.flush();
        String jsonResponse = sw.toString();
        assertTrue(jsonResponse.contains("\"isInWishList\":false"),
                "La risposta JSON deve contenere isInWishList = false");
    }

    @Test
    void testDoGet_AdminUser_ForwardsToAdminHomepage() throws ServletException, IOException {
        // 1) Admin user in session
        Utente admin = new Utente();
        admin.setEmail("admin@example.com");
        admin.setTipo("Gestore-Admin");
        when(session.getAttribute("utente")).thenReturn(admin);

        when(request.getParameter("isbn")).thenReturn("123");
        
        Libro mockLibro = new Libro();
        mockLibro.setIsbn("123");
        when(mockLibroDAO.doRetrieveById("123")).thenReturn(mockLibro);

        // 2) Mock dispatcher
        jakarta.servlet.RequestDispatcher dispatcher = mock(jakarta.servlet.RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        // 3) Execute
        servletUnderTest.doGet(request, response);

        // 4) Verify forward to admin page
        verify(dispatcher).forward(request, response);
        verify(response, never()).getWriter();
    }

    @Test
    void testDoGet_NullWishList_InitializesNewWishList() throws ServletException, IOException {
        // 1) Parameters
        String isbn = "978-1234567890";
        when(request.getParameter("isbn")).thenReturn(isbn);
        
        Libro mockLibro = new Libro();
        mockLibro.setIsbn(isbn);
        when(mockLibroDAO.doRetrieveById(isbn)).thenReturn(mockLibro);

        // 2) User logged in
        Utente utente = new Utente();
        utente.setEmail("user@example.com");
        utente.setTipo("Cliente");
        when(session.getAttribute("utente")).thenReturn(utente);

        // 3) WishList is null in session
        WishList wishList = new WishList();
        when(session.getAttribute("wishList")).thenReturn(wishList);

        // 4) Simulate writer
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // 5) Execute
        servletUnderTest.doGet(request, response);

        // 6) Verify wishList.libri was initialized and book added
        assertNotNull(wishList.getLibri(), "Libri list should be initialized");
        assertEquals(1, wishList.getLibri().size(), "Should contain 1 book");
        assertEquals(isbn, wishList.getLibri().get(0).getIsbn());

        // 7) Verify session.setAttribute was called
        verify(session).setAttribute("wishList", wishList);

        // 8) Verify content type was set
        verify(response).setContentType("application/json");

        // 9) Verify JSON response
        pw.flush();
        String jsonResponse = sw.toString();
        assertTrue(jsonResponse.contains("\"isInWishList\":true"));
    }

    @Test
    void testDoGet_WishListWithNullLibri_InitializesLibriList() throws ServletException, IOException {
        // 1) Parameters
        String isbn = "978-9999999999";
        when(request.getParameter("isbn")).thenReturn(isbn);
        
        Libro mockLibro = new Libro();
        mockLibro.setIsbn(isbn);
        when(mockLibroDAO.doRetrieveById(isbn)).thenReturn(mockLibro);

        // 2) User logged in
        Utente utente = new Utente();
        utente.setEmail("user@example.com");
        utente.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(utente);

        // 3) WishList exists but getLibri() returns null
        WishList wishList = new WishList();
        wishList.setLibri(null);
        when(session.getAttribute("wishList")).thenReturn(wishList);

        // 4) Simulate writer
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        // 5) Execute
        servletUnderTest.doGet(request, response);

        // 6) Verify libri list was initialized and book added
        assertNotNull(wishList.getLibri(), "Libri should be initialized");
        assertEquals(1, wishList.getLibri().size());
        assertEquals(isbn, wishList.getLibri().get(0).getIsbn());

        // 7) Verify session.setAttribute was called
        verify(session).setAttribute("wishList", wishList);

        // 8) Verify content type was set
        verify(response).setContentType("application/json");

        // 9) Verify JSON response
        pw.flush();
        String jsonResponse = sw.toString();
        assertTrue(jsonResponse.contains("\"isInWishList\":true"));
    }

}