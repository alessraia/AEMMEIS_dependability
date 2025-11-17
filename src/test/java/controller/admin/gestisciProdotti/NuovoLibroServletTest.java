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
}