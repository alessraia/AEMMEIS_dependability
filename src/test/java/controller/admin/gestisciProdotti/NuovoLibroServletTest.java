package controller.admin.gestisciProdotti;

import controller.admin.gestisciProdotti.NuovoLibroServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.mockito.Mockito.*;

class NuovoLibroServletTest {

    private NuovoLibroServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private LibroDAO libroDAO;

    @BeforeEach
    void setUp() {
        servlet = new NuovoLibroServlet();

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        // Se usi un LibroDAO fittizio (mock) interno alla Servlet, potresti dover modificare il codice
        // o passarlo come dipendenza (injection) per testare meglio. Per ora facciamo finta di no.
        libroDAO = mock(LibroDAO.class);
        doNothing().when(libroDAO).doSave(any(Libro.class));
        when(request.getSession()).thenReturn(session);
        servlet.setLibroDAO(libroDAO);
    }

    @Test
    void testDoGet_Success() throws Exception {
        // Simuliamo l'invio di parametri validi
        when(request.getParameter("isbn")).thenReturn("1234123412341");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");

        // Parametri autore
        when(request.getParameterValues("nome")).thenReturn(new String[]{"NomeAutore"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});

        // Lista di libri già presenti (vuota per far sì che l'inserimento vada a buon fine)
        when(libroDAO.doRetriveAll()).thenReturn(java.util.Collections.emptyList());

        // Non potendo usare la doGet(...) con injection di libroDAO, ipotizziamo che la Servlet lo crei internamente.
        // Se la Servlet “fissa” fa new LibroDAO(), non possiamo mockarlo direttamente
        // a meno di cambiare design (es. con Dependency Injection).

        // Se l’inserimento va a buon fine, la Servlet fa response.sendRedirect("gestisci-prodotti");
        // Verifichiamo di non avere forward su errori
        servlet.doGet(request, response);

        // Verifica che abbia fatto la redirect
        verify(response).sendRedirect("gestisci-prodotti");
        verify(dispatcher, never()).forward(request, response);
    }

    @Test
    void testDoGet_FormNonValido() throws Exception {
        // Simuliamo l'invio di parametri con un anno di pubblicazione errato (vuoto)
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn(""); // ERRORE
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");

        // Simuliamo che la request dispatcher punti a una certa pagina d’errore
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // Verifichiamo che sia stato eseguito il forward alla pagina di errore
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    @Test
    void testDoGet_LibroGiaPresente() throws Exception {
        // Parametri validi
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{"NomeAutore"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});

        // Simuliamo che il libro con ISBN 1234512341234 sia già presente
        // (creiamo un Libro e lo mettiamo nella lista)
        model.libroService.Libro libroEsistente = new model.libroService.Libro();
        libroEsistente.setIsbn("1234512341234");
        java.util.List<model.libroService.Libro> lista = new java.util.ArrayList<>();
        lista.add(libroEsistente);

        // Mock del libroDAO
        when(libroDAO.doRetriveAll()).thenReturn(lista);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/nuovoProdotto.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(request).setAttribute("esito", "non riuscito");
    }

    /**
     * Test when sconto/prezzo validation fails (empty sconto, invalid sconto, zero/negative prezzo)
     * Expected: forward to error page
     */
    @Test
    void testDoGet_ScontoOrPrezzoInvalid() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("150"); // Invalid: > 100
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when author fields are empty
     * Expected: forward to error page
     */
    @Test
    void testDoGet_AuthorFieldsEmpty() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{""}); // Empty nome
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when prezzo cannot be parsed as double (NumberFormatException)
     * Expected: forward to error page
     */
    @Test
    void testDoGet_NumberFormatException_Prezzo() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("invalid_price"); // Invalid number format
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test isScontoValid with non-numeric string to cover return false branch
     * Expected: returns false
     */
    @Test
    void testIsScontoValid_NonNumeric() {
        assertFalse(servlet.isScontoValid("abc"));
    }

    /**
     * Test isAnnoPubblicazioneValid with non-numeric string to cover return false branch
     * Expected: returns false
     */
    @Test
    void testIsAnnoPubblicazioneValid_NonNumeric() {
        assertFalse(servlet.isAnnoPubblicazioneValid("abc"));
    }

    /**
     * Test with null author arrays (no authors provided)
     * Expected: libro is saved without authors
     */
    @Test
    void testDoGet_NoAuthors() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(null); // No authors
        when(request.getParameterValues("cognome")).thenReturn(null);
        when(request.getParameterValues("cf")).thenReturn(null);
        when(libroDAO.doRetriveAll()).thenReturn(java.util.Collections.emptyList());

        servlet.doGet(request, response);

        verify(response).sendRedirect("gestisci-prodotti");
    }

    /**
     * Test with ISBN length not equal to 13
     * Expected: forward to error page
     */
    @Test
    void testDoGet_InvalidISBNLength() throws Exception {
        when(request.getParameter("isbn")).thenReturn("12345"); // Invalid: length != 13
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when ISBN is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_ISBNNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn(null);
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when titolo is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_TitoloNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn(null);
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when titolo is empty
     * Expected: forward to error page
     */
    @Test
    void testDoGet_TitoloEmpty() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when genere is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_GenereNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn(null);
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when genere is empty
     * Expected: forward to error page
     */
    @Test
    void testDoGet_GenereEmpty() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when annoPubb is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_AnnoPubbNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn(null);
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when prezzo is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_PrezzoNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn(null);
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when prezzo is empty
     * Expected: forward to error page
     */
    @Test
    void testDoGet_PrezzoEmpty() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when sconto is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_ScontoNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn(null);
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when trama is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_TramaNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn(null);
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when immagine is null
     * Expected: forward to error page
     */
    @Test
    void testDoGet_ImmagineNull() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test boundary condition: prezzo = 0 should be rejected
     * Covers boundary mutation on line 54: prezzo > 0
     */
    @Test
    void testDoGet_PrezzoZero_ShouldRejectAndNotSave() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("0"); // boundary case: prezzo > 0
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{"NomeAutore"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // Should forward to error page, not save
        verify(dispatcher).forward(request, response);
        verify(libroDAO, never()).doSave(any(Libro.class));
    }

    /**
     * Test doPost delegates to doGet
     * Expected: doGet behavior is invoked
     */
    @Test
    void testDoPost() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{"NomeAutore"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});
        when(libroDAO.doRetriveAll()).thenReturn(java.util.Collections.emptyList());

        servlet.doPost(request, response);

        verify(response).sendRedirect("gestisci-prodotti");
    }

    /**
     * Test boundary condition: sconto = 0 should be rejected
     * Covers boundary mutation on line 54: sconto > 0
     */
    @Test
    void testDoGet_ScontoZero_ShouldRejectAndNotSave() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("prezzo")).thenReturn("19.99");
        when(request.getParameter("sconto")).thenReturn("0"); // boundary case
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{"NomeAutore"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"CognomeAutore"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"XYZ123"});
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // Should forward to error page, not save
        verify(dispatcher).forward(request, response);
        verify(libroDAO, never()).doSave(any(Libro.class));
    }

    /**
     * Test that verifies doSave is actually called (line 107)
     * Uses MockedConstruction to capture Libro objects and verify all fields
     */
    @Test
    void testDoGet_Success_VerifyAllLibroFieldsSet() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2020");
        when(request.getParameter("prezzo")).thenReturn("25.50");
        when(request.getParameter("sconto")).thenReturn("15");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        when(request.getParameterValues("nome")).thenReturn(new String[]{"Mario"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"Rossi"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"RSSMRA80A01H123Z"});
        when(libroDAO.doRetriveAll()).thenReturn(java.util.Collections.emptyList());

        servlet.doGet(request, response);

        // Verify doSave was called with a Libro that has all fields set correctly
        verify(libroDAO).doSave(argThat(libro ->
            libro.getIsbn().equals("1234512341234") &&
            libro.getTitolo().equals("Titolo Test") &&
            libro.getGenere().equals("Genere Test") &&
            libro.getAnnoPubblicazioni().equals("2020") &&
            libro.getPrezzo() == 25.50 &&
            libro.getSconto() == 15 &&
            libro.getTrama().equals("Trama di prova") &&
            libro.getImmagine().equals("cover.jpg") &&
            libro.isDisponibile() && // Verifies setDisponibile(true) was called
            libro.getAutori() != null && libro.getAutori().size() == 1
        ));
        
        verify(response).sendRedirect("gestisci-prodotti");
    }

    /**
     * Test boundary: isScontoValid with exactly 100 (should be valid)
     * Covers boundary mutation on line 121: strInt <= 100
     */
    @Test
    void testIsScontoValid_Boundary100() {
        assertTrue(servlet.isScontoValid("100"));
    }

    /**
     * Test boundary: isScontoValid with 101 (should be invalid)
     * Covers boundary mutation on line 121: strInt <= 100
     */
    @Test
    void testIsScontoValid_Boundary101() {
        assertFalse(servlet.isScontoValid("101"));
    }

    /**
     * Test boundary: isScontoValid with 1 (should be valid)
     * Covers boundary mutation on line 121: strInt > 0
     */
    @Test
    void testIsScontoValid_Boundary1() {
        assertTrue(servlet.isScontoValid("1"));
    }

    /**
     * Test boundary: isAnnoPubblicazioneValid with negative year (should be invalid)
     * Covers boundary mutation on line 129: strInt > 0
     */
    @Test
    void testIsAnnoPubblicazioneValid_NegativeYear() {
        assertFalse(servlet.isAnnoPubblicazioneValid("-2020"));
    }

    /**
     * Test boundary: isAnnoPubblicazioneValid with year 0 (should be invalid)
     * Covers boundary mutation on line 129: strInt > 0
     */
    @Test
    void testIsAnnoPubblicazioneValid_ZeroYear() {
        assertFalse(servlet.isAnnoPubblicazioneValid("0"));
    }

    /**
     * Test boundary: isAnnoPubblicazioneValid with year 1 (should be valid)
     * Covers boundary mutation on line 129: strInt > 0
     */
    @Test
    void testIsAnnoPubblicazioneValid_OneYear() {
        assertTrue(servlet.isAnnoPubblicazioneValid("1"));
    }

    /**
     * Test boundary: isAnnoPubblicazioneValid with future year (should be invalid)
     * Covers boundary mutation on line 129: strInt <= LocalDateTime.now().getYear()
     */
    @Test
    void testIsAnnoPubblicazioneValid_FutureYear() {
        int futureYear = java.time.LocalDateTime.now().getYear() + 1;
        assertFalse(servlet.isAnnoPubblicazioneValid(String.valueOf(futureYear)));
    }

    /**
     * Test boundary: isAnnoPubblicazioneValid with current year (should be valid)
     * Covers boundary mutation on line 129: strInt <= LocalDateTime.now().getYear()
     */
    @Test
    void testIsAnnoPubblicazioneValid_CurrentYear() {
        int currentYear = java.time.LocalDateTime.now().getYear();
        assertTrue(servlet.isAnnoPubblicazioneValid(String.valueOf(currentYear)));
    }

    /**
     * Test that all Autore fields are properly set (lines 78-80)
     * Covers SURVIVED mutations on setNome, setCognome, setCf
     */
    @Test
    void testDoGet_Success_VerifyAutoreFieldsSet() throws Exception {
        when(request.getParameter("isbn")).thenReturn("1234512341234");
        when(request.getParameter("titolo")).thenReturn("Titolo Test");
        when(request.getParameter("genere")).thenReturn("Genere Test");
        when(request.getParameter("annoPubb")).thenReturn("2020");
        when(request.getParameter("prezzo")).thenReturn("25.50");
        when(request.getParameter("sconto")).thenReturn("15");
        when(request.getParameter("trama")).thenReturn("Trama di prova");
        when(request.getParameter("immagine")).thenReturn("cover.jpg");
        
        // Multiple authors
        when(request.getParameterValues("nome")).thenReturn(new String[]{"Mario", "Giovanni"});
        when(request.getParameterValues("cognome")).thenReturn(new String[]{"Rossi", "Bianchi"});
        when(request.getParameterValues("cf")).thenReturn(new String[]{"RSSMRA80A01H123Z", "BNCGNN90B02I456Y"});
        
        when(libroDAO.doRetriveAll()).thenReturn(java.util.Collections.emptyList());

        servlet.doGet(request, response);

        // Verify doSave was called with a Libro that has authors with all fields set
        verify(libroDAO).doSave(argThat(libro ->
            libro.getAutori() != null && 
            libro.getAutori().size() == 2 &&
            // First author verification
            libro.getAutori().get(0).getNome().equals("Mario") &&
            libro.getAutori().get(0).getCognome().equals("Rossi") &&
            libro.getAutori().get(0).getCf().equals("RSSMRA80A01H123Z") &&
            // Second author verification
            libro.getAutori().get(1).getNome().equals("Giovanni") &&
            libro.getAutori().get(1).getCognome().equals("Bianchi") &&
            libro.getAutori().get(1).getCf().equals("BNCGNN90B02I456Y")
        ));
        
        verify(response).sendRedirect("gestisci-prodotti");
    }

    private void assertTrue(boolean condition) {
        if (!condition) {
            throw new AssertionError("Expected true but was false");
        }
    }

    private void assertFalse(boolean condition) {
        if (condition) {
            throw new AssertionError("Expected false but was true");
        }
    }
}