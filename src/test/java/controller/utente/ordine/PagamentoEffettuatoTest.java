package controller.utente.ordine;

import controller.utente.ordine.PagamentoEffettuato;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.ordineService.Ordine;
import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.mockito.Mockito;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class PagamentoEffettuatoTest {

    private PagamentoEffettuato servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private TesseraDAO tesseraDAO;

    @BeforeEach
    void setUp() {
        servletUnderTest = new PagamentoEffettuato();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        tesseraDAO = mock(TesseraDAO.class);
        
        servletUnderTest.setTesseraDAO(tesseraDAO);
        when(request.getSession()).thenReturn(session);
    }

    /**
     * Flusso alternativo: campi carta errati
     * UC_GO_4.2 scenario 3.a
     */
    @Test
    void testDoGet_InvalidCardData() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(user);
        // Parametri carta
        when(request.getParameter("cardName")).thenReturn("");
        when(request.getParameter("cardNumber")).thenReturn("abc123");
        when(request.getParameter("expiryDate")).thenReturn(null);
        when(request.getParameter("cvv")).thenReturn("xyz");
        when(request.getParameter("costo")).thenReturn("1.0");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: premium con punti > disponibili (UC_GO_4.4 scenario 4.a1)
     */
    @Test
    void testDoGet_InvalidPoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        Tessera tessera = new Tessera();
        tessera.setPunti(900);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Simuliamo che l'utente inserisce 999 punti, ma in DB ne ha meno
        when(request.getParameter("punti")).thenReturn("999");
        // Campi carta validi
        when(request.getParameter("cardName")).thenReturn("Mario Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("costo")).thenReturn("1.0");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso principale: utente standard con campi validi -> ordineEffettuato.jsp
     */
    @Test
    void testDoGet_SuccessStandard() throws ServletException, IOException {
        Utente standardUser = new Utente();
        standardUser.setTipo("standard");
        standardUser.setEmail("mario@example.com");
        when(session.getAttribute("utente")).thenReturn(standardUser);

        when(request.getParameter("cardName")).thenReturn("Mario Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");

        // Indirizzo e costo
        when(request.getParameter("indirizzo")).thenReturn("Via Prova 1");
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("costo")).thenReturn("39.90");

        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(dispatcher);

        // Capture the ordine object set in request
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);

        servletUnderTest.doGet(request, response);

        // Verify that setAttribute was called with "ordine" and capture the value
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        // Verify the Ordine object has correct values (kills mutants on lines 37-39)
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertNotNull(capturedOrdine);
        assertEquals("Roma", capturedOrdine.getCitta());
        assertEquals("Via Prova 1", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(39.90, capturedOrdine.getCosto(), 0.01);
        assertEquals(0, capturedOrdine.getPuntiSpesi()); // Standard user has 0 points

        verify(dispatcher).forward(request, response);
    }

    /**
     * Test per verificare il comportamento con utente premium che usa punti validi
     * Questo test uccide i mutanti su setPuntiSpesi (line 60)
     */
    @Test
    void testDoGet_PremiumUserWithValidPoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(1000);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        when(request.getParameter("punti")).thenReturn("500");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("indirizzo")).thenReturn("Via Test 1");
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("costo")).thenReturn("50.00");

        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(dispatcher);

        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);

        servletUnderTest.doGet(request, response);

        // Verify setAttribute was called and capture ordine
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        // Verify setPuntiSpesi was called with correct value (kills mutant on line 60)
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals(500, capturedOrdine.getPuntiSpesi());
        assertEquals("Milano", capturedOrdine.getCitta());
        assertEquals("Via Test 1", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(50.00, capturedOrdine.getCosto(), 0.01);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Test per boundary condition: punti negativi (line 47 - negated conditional and boundary)
     */
    @Test
    void testDoGet_NegativePoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(500);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Punti negativi - should trigger error
        when(request.getParameter("punti")).thenReturn("-1");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("costo")).thenReturn("50.00");

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(errorDispatcher);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(errorDispatcher).forward(request, response);
    }

    /**
     * Test per boundary condition: punti = 0 (valore minimo valido)
     * Testa il boundary della condizione punti < 0 (line 47)
     */
    @Test
    void testDoGet_ZeroPoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(500);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Punti = 0 - dovrebbe essere accettato (minimo valido)
        when(request.getParameter("punti")).thenReturn("0");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("indirizzo")).thenReturn("Via Test 0");
        when(request.getParameter("citta")).thenReturn("Firenze");
        when(request.getParameter("costo")).thenReturn("30.00");

        RequestDispatcher successDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(successDispatcher);

        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);

        servletUnderTest.doGet(request, response);

        // Verify success path
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        verify(request, never()).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(successDispatcher).forward(request, response);
        
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals(0, capturedOrdine.getPuntiSpesi());
    }

    /**
     * Test per boundary condition: punti esattamente uguali al massimo disponibile
     * Testa il boundary della condizione (line 47 - changed conditional boundary)
     */
    @Test
    void testDoGet_PointsEqualToMax() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(1000);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Punti esattamente uguali al massimo - dovrebbe essere accettato
        when(request.getParameter("punti")).thenReturn("1000");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("indirizzo")).thenReturn("Via Test 2");
        when(request.getParameter("citta")).thenReturn("Napoli");
        when(request.getParameter("costo")).thenReturn("100.00");

        RequestDispatcher successDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(successDispatcher);

        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);

        servletUnderTest.doGet(request, response);

        // Verify success path: setAttribute is called and success dispatcher is used
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        verify(request, never()).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(successDispatcher).forward(request, response);
        
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals(1000, capturedOrdine.getPuntiSpesi());
    }

    /**
     * Test per boundary condition: punti esattamente massimo + 1 (line 47 - changed conditional boundary)
     * Verifica che punti > max sia rifiutato (testa che la condizione sia > e non >=)
     */
    @Test
    void testDoGet_PointsOneOverMax() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(1000);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Punti = max + 1 - dovrebbe essere rifiutato
        when(request.getParameter("punti")).thenReturn("1001");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("costo")).thenReturn("100.00");

        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(errorDispatcher);

        servletUnderTest.doGet(request, response);

        // Dovrebbe inoltrare alla pagina di errore, non a quella di successo
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(request, never()).getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp");
        verify(errorDispatcher).forward(request, response);
        verify(request, never()).setAttribute(eq("ordine"), any());
    }

    /**
     * Test per utente premium con stringa punti vuota (line 45 - negated conditional)
     * La stringa vuota dovrebbe essere gestita correttamente
     */
    @Test
    void testDoGet_PremiumUserWithEmptyPoints() throws ServletException, IOException {
        Utente premiumUser = new Utente();
        premiumUser.setTipo("Premium");
        premiumUser.setEmail("alice@gmail.com");
        when(session.getAttribute("utente")).thenReturn(premiumUser);
        
        Tessera tessera = new Tessera();
        tessera.setPunti(1000);
        when(tesseraDAO.doRetrieveByEmail("alice@gmail.com")).thenReturn(tessera);

        // Empty string should be accepted
        when(request.getParameter("punti")).thenReturn("");
        when(request.getParameter("cardName")).thenReturn("Alice Rossi");
        when(request.getParameter("cardNumber")).thenReturn("1234567890123456");
        when(request.getParameter("expiryDate")).thenReturn("2025-12-31");
        when(request.getParameter("cvv")).thenReturn("123");
        when(request.getParameter("indirizzo")).thenReturn("Via Test 3");
        when(request.getParameter("citta")).thenReturn("Torino");
        when(request.getParameter("costo")).thenReturn("25.00");

        when(request.getRequestDispatcher("/WEB-INF/results/ordineEffettuato.jsp"))
                .thenReturn(dispatcher);

        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);

        servletUnderTest.doGet(request, response);

        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals(0, capturedOrdine.getPuntiSpesi()); // Empty string -> 0 points

        verify(dispatcher).forward(request, response);
    }

}

